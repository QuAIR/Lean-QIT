/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.SymmetricSubspace
public import QIT.Classical.Ensemble
public import QIT.Classical.CQState
public import QIT.Channels.Diamond
public import QIT.States.Purification.Canonical
public import QIT.States.Purification.Equivalence
public import QIT.States.Schatten
public import QIT.States.Subnormalized
public import QIT.States.TraceNorm.PositivePart

/-!
# Quantum de Finetti representation

Permutation-invariant states are approximated by mixtures of i.i.d. states
(renner-2007-symmetry-independence, sub.tex:618 thm:main;
christandl-koenig-renner-2008-postselection, .tex:291 thm:main).

The full de Finetti/post-selection proof is intentionally not stated here.
This module currently exposes only the route surface that imports the symmetric
tensor-power support.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v}
variable [Fintype ι] [Fintype a] [DecidableEq a]

namespace TensorPower

/-- A nonempty base alphabet gives a nonempty tensor-power basis at every
block length. -/
protected theorem nonempty [Nonempty a] : (n : ℕ) → Nonempty (TensorPower a n)
  | 0 => ⟨⟨⟩⟩
  | n + 1 =>
      let hn := TensorPower.nonempty n
      ⟨(Classical.choice ‹Nonempty a›, Classical.choice hn)⟩

end TensorPower

instance tensorPowerNonempty [Nonempty a] (n : ℕ) : Nonempty (TensorPower a n) :=
  TensorPower.nonempty (a := a) n

namespace TensorPowerProfile

/-- A nonempty base alphabet gives at least one realized tensor-power profile. -/
protected theorem nonempty [Nonempty a] (n : ℕ) : Nonempty (TensorPowerProfile a n) := by
  let x : TensorPower a n := Classical.choice (TensorPower.nonempty n)
  exact ⟨⟨tensorPowerTypeProfile (a := a) n x,
    tensorPowerTypeProfile_mem_profiles (a := a) n x⟩⟩

theorem card_ne_zero [Nonempty a] (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) ≠ 0 :=
  letI : Nonempty (TensorPowerProfile a n) := TensorPowerProfile.nonempty (a := a) n
  Fintype.card_ne_zero

theorem card_pos [Nonempty a] (n : ℕ) :
    0 < Fintype.card (TensorPowerProfile a n) :=
  Nat.pos_of_ne_zero (TensorPowerProfile.card_ne_zero (a := a) n)

end TensorPowerProfile

/-- Split a function on `Fin (n+k)` into its first `n` and last `k`
coordinates. This is the `Fin`-level bookkeeping behind Renner's
`tr_k` convention [Renner2007Symmetry, sub.tex:618-633]. -/
def finTakeDropEquiv (n k : ℕ) :
    (Fin (n + k) → a) ≃ Prod (Fin n → a) (Fin k → a) where
  toFun f := (fun i => f (Fin.castAdd k i), fun j => f (Fin.natAdd n j))
  invFun g := fun i => Fin.addCases (fun j : Fin n => g.1 j) (fun j : Fin k => g.2 j) i
  left_inv := by
    intro f
    ext i
    exact Fin.addCases
      (motive := fun i =>
        Fin.addCases (fun j : Fin n => f (Fin.castAdd k j))
          (fun j : Fin k => f (Fin.natAdd n j)) i = f i)
      (fun j => by simp)
      (fun j => by simp)
      i
  right_inv := by
    intro g
    ext i <;> simp

/-- Source-shaped split of a tensor power into retained `n` systems and traced
`k` systems. -/
def tensorPowerTakeDropEquiv (a : Type v) [Fintype a] [DecidableEq a]
    (n k : ℕ) :
    TensorPower a (n + k) ≃ Prod (TensorPower a n) (TensorPower a k) :=
  (tensorPowerEquiv (a := a) (n + k)).trans
    ((finTakeDropEquiv (a := a) n k).trans
      (Equiv.prodCongr (tensorPowerEquiv (a := a) n).symm
        (tensorPowerEquiv (a := a) k).symm))

@[simp]
theorem tensorPowerTakeDropEquiv_fst_apply (n k : ℕ)
    (x : TensorPower a (n + k)) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerTakeDropEquiv a n k x).1) i =
      tensorPowerEquiv (n + k) x (Fin.castAdd k i) := by
  simp [tensorPowerTakeDropEquiv, finTakeDropEquiv]

@[simp]
theorem tensorPowerTakeDropEquiv_snd_apply (n k : ℕ)
    (x : TensorPower a (n + k)) (j : Fin k) :
    tensorPowerEquiv k ((tensorPowerTakeDropEquiv a n k x).2) j =
      tensorPowerEquiv (n + k) x (Fin.natAdd n j) := by
  simp [tensorPowerTakeDropEquiv, finTakeDropEquiv]

private theorem fin_prod_univ_add {M : Type _} [CommMonoid M] (n k : ℕ)
    (f : Fin (n + k) → M) :
    (∏ i : Fin (n + k), f i) =
      (∏ i : Fin n, f (Fin.castAdd k i)) *
        (∏ j : Fin k, f (Fin.natAdd n j)) := by
  calc
    (∏ i : Fin (n + k), f i) =
        ∏ s : Sum (Fin n) (Fin k), f (finSumFinEquiv s) := by
          refine (Finset.prod_equiv finSumFinEquiv ?_ ?_).symm
          · intro s
            simp
          · intro s hs
            rfl
    _ = (∏ i : Fin n, f (Fin.castAdd k i)) *
          (∏ j : Fin k, f (Fin.natAdd n j)) := by
          simp [Fintype.prod_sum_type, finSumFinEquiv_apply_left,
            finSumFinEquiv_apply_right]

namespace PureVector

variable {b : Type w} [Fintype b] [DecidableEq b]

/-- Product of normalized pure vectors. -/
def prod (ψ : PureVector a) (φ : PureVector b) : PureVector (Prod a b) where
  amp x := ψ.amp x.1 * φ.amp x.2
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace]
    calc
      (fun x : Prod a b => ψ.amp x.1 * φ.amp x.2) ⬝ᵥ
          (fun x : Prod a b => star (ψ.amp x.1 * φ.amp x.2)) =
          (∑ i : a, ψ.amp i * star (ψ.amp i)) *
            (∑ j : b, φ.amp j * star (φ.amp j)) := by
            rw [dotProduct, Fintype.sum_prod_type]
            simp only [star_mul]
            calc
              (∑ x : a, ∑ y : b,
                  ψ.amp x * φ.amp y * (star (φ.amp y) * star (ψ.amp x))) =
                  ∑ x : a, (ψ.amp x * star (ψ.amp x)) *
                    (∑ y : b, φ.amp y * star (φ.amp y)) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    calc
                      (∑ y : b, ψ.amp x * φ.amp y *
                          (star (φ.amp y) * star (ψ.amp x))) =
                          ∑ y : b, (ψ.amp x * star (ψ.amp x)) *
                            (φ.amp y * star (φ.amp y)) := by
                            apply Finset.sum_congr rfl
                            intro y hy
                            ring
                      _ = (ψ.amp x * star (ψ.amp x)) *
                            (∑ y : b, φ.amp y * star (φ.amp y)) := by
                            rw [Finset.mul_sum]
              _ = (∑ i : a, ψ.amp i * star (ψ.amp i)) *
                    (∑ j : b, φ.amp j * star (φ.amp j)) := by
                    rw [Finset.sum_mul]
      _ = (rankOneMatrix ψ.amp).trace * (rankOneMatrix φ.amp).trace := by
            simp [rankOneMatrix_trace, dotProduct]
      _ = 1 := by rw [ψ.trace_rankOne_eq_one, φ.trace_rankOne_eq_one, mul_one]

@[simp]
theorem prod_amp (ψ : PureVector a) (φ : PureVector b) (x : Prod a b) :
    (ψ.prod φ).amp x = ψ.amp x.1 * φ.amp x.2 := rfl

/-- Product pure vectors induce product density states. -/
theorem prod_state (ψ : PureVector a) (φ : PureVector b) :
    (ψ.prod φ).state = ψ.state.prod φ.state := by
  apply State.ext
  ext i j
  simp [PureVector.state, State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    rankOneMatrix_apply, mul_assoc, mul_left_comm, mul_comm]

/-- IID tensor power of a normalized pure vector. -/
def tensorPower (ψ : PureVector a) : (n : ℕ) → PureVector (TensorPower a n)
  | 0 =>
      { amp := fun _ => 1
        trace_rankOne_eq_one := by
          rw [rankOneMatrix_trace]
          change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
          simp }
  | n + 1 => ψ.prod (tensorPower ψ n)

@[simp]
theorem tensorPower_zero (ψ : PureVector a) :
    ψ.tensorPower 0 =
      ({ amp := fun _ : PUnit => 1
         trace_rankOne_eq_one := by
          rw [rankOneMatrix_trace]
          change (∑ _ : PUnit, (1 : ℂ) * star (1 : ℂ)) = 1
          simp } : PureVector (TensorPower a 0)) := rfl

@[simp]
theorem tensorPower_succ (ψ : PureVector a) (n : ℕ) :
    ψ.tensorPower (n + 1) = ψ.prod (ψ.tensorPower n) := rfl

theorem tensorPower_state (ψ : PureVector a) :
    (n : ℕ) → (ψ.tensorPower n).state = ψ.state.tensorPower n
  | 0 => by
      apply State.ext
      ext i j
      cases i
      cases j
      simp [PureVector.tensorPower, PureVector.state, State.tensorPower, State.unit,
        rankOneMatrix_apply]
  | n + 1 => by
      rw [PureVector.tensorPower_succ, State.tensorPower_succ]
      calc
        (ψ.prod (ψ.tensorPower n)).state =
            ψ.state.prod (ψ.tensorPower n).state := PureVector.prod_state ψ (ψ.tensorPower n)
        _ = ψ.state.prod (ψ.state.tensorPower n) := by rw [tensorPower_state ψ n]

/-- Renner's rank-one-projector version of an `m`-IID vector, in the typed
`m+r` tensor-power form. It says that after some permutation, the rank-one
state of `ψ` is a product of `ν^⊗m` and an arbitrary residual pure state.
This is the finite Lean form of the definition preceding
Theorem `thm:main` [Renner2007Symmetry, sub.tex:608-611]. -/
def IsRennerMIIDIn {m r : ℕ} (ψ : PureVector (TensorPower a (m + r)))
    (ν : PureVector a) : Prop :=
  ∃ σ : Equiv.Perm (Fin (m + r)), ∃ η : PureVector (TensorPower a r),
    ψ.state =
      (((ν.tensorPower m).prod η).reindex
        (tensorPowerTakeDropEquiv a m r).symm).state.reindex
          (permEquiv (a := a) (m + r) σ).symm

end PureVector

namespace State

/-- Reindexing by an equivalence inverse and then by the equivalence returns
the original state. -/
theorem reindex_symm_reindex {α : Type u} {β : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State β) (e : α ≃ β) :
    (ρ.reindex e.symm).reindex e = ρ := by
  apply State.ext
  ext i j
  simp [State.reindex]

/-- Product-state marginal on the left subsystem. -/
theorem marginalA_prod {α : Type u} {β : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State α) (σ : State β) :
    (ρ.prod σ).marginalA = ρ := by
  apply State.ext
  exact State.partialTraceB_prod ρ σ

/-- IID tensor powers factor across the `n|k` tensor-power split. -/
theorem tensorPower_reindex_takeDrop (ρ : State a) (n k : ℕ) :
    (ρ.tensorPower (n + k)).reindex (tensorPowerTakeDropEquiv a n k) =
      (ρ.tensorPower n).prod (ρ.tensorPower k) := by
  apply State.ext
  ext x y
  simp only [State.reindex_matrix, Matrix.submatrix_apply]
  rw [State.tensorPower_matrix_apply, State.prod]
  change
    (∏ i : Fin (n + k),
        ρ.matrix
          (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x) i)
          (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y) i)) =
      (ρ.tensorPower n).matrix x.1 y.1 * (ρ.tensorPower k).matrix x.2 y.2
  rw [fin_prod_univ_add n k]
  rw [State.tensorPower_matrix_apply ρ n, State.tensorPower_matrix_apply ρ k]
  have hleft :
      (∏ i : Fin n,
          ρ.matrix
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
              (Fin.castAdd k i))
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
              (Fin.castAdd k i))) =
        ∏ i : Fin n, ρ.matrix (tensorPowerEquiv n x.1 i) (tensorPowerEquiv n y.1 i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hx := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) i
    have hy := tensorPowerTakeDropEquiv_fst_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) i
    simp at hx hy
    rw [← hx, ← hy]
  have hright :
      (∏ j : Fin k,
          ρ.matrix
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm x)
              (Fin.natAdd n j))
            (tensorPowerEquiv (n + k) ((tensorPowerTakeDropEquiv a n k).symm y)
              (Fin.natAdd n j))) =
        ∏ j : Fin k, ρ.matrix (tensorPowerEquiv k x.2 j) (tensorPowerEquiv k y.2 j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hx := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm x) j
    have hy := tensorPowerTakeDropEquiv_snd_apply (a := a) n k
      ((tensorPowerTakeDropEquiv a n k).symm y) j
    simp at hx hy
    rw [← hx, ← hy]
  rw [hleft, hright]

/-- Trace out the last `k` tensor factors of a state on `a^(n+k)`, using the
project tensor-power convention. -/
def traceOutLastK {n k : ℕ} (ρ : State (TensorPower a (n + k))) :
    State (TensorPower a n) :=
  (ρ.reindex (tensorPowerTakeDropEquiv a n k)).marginalA

@[simp]
theorem traceOutLastK_matrix {n k : ℕ} (ρ : State (TensorPower a (n + k))) :
    (ρ.traceOutLastK (a := a) (n := n) (k := k)).matrix =
      partialTraceB (a := TensorPower a n) (b := TensorPower a k)
        ((ρ.reindex (tensorPowerTakeDropEquiv a n k)).matrix) := rfl

/-- Tracing out the last `k` factors of a product state written across the
`n|k` split returns the retained state. -/
theorem traceOutLastK_reindex_split_prod {n k : ℕ}
    (ρ : State (TensorPower a n)) (σ : State (TensorPower a k)) :
    traceOutLastK (a := a) (n := n) (k := k)
        ((ρ.prod σ).reindex (tensorPowerTakeDropEquiv a n k).symm) = ρ := by
  simp [traceOutLastK, State.reindex_symm_reindex, State.marginalA_prod]

/-- Tracing out the final `k` systems of an IID tensor power leaves the retained
`n`-fold IID tensor power. -/
theorem traceOutLastK_tensorPower (ρ : State a) (n k : ℕ) :
    traceOutLastK (a := a) (n := n) (k := k) (ρ.tensorPower (n + k)) =
      ρ.tensorPower n := by
  simp [traceOutLastK, State.tensorPower_reindex_takeDrop, State.marginalA_prod]

/-- Tracing out the residual factor of a split product pure state preserves the
rank-one retained component. -/
theorem traceOutLastK_pure_prod {n k : ℕ}
    (ψ : PureVector (TensorPower a n)) (η : PureVector (TensorPower a k)) :
    traceOutLastK (a := a) (n := n) (k := k)
        (((ψ.prod η).state).reindex (tensorPowerTakeDropEquiv a n k).symm) =
      ψ.state := by
  rw [PureVector.prod_state, traceOutLastK_reindex_split_prod]

/-- A rank-one state whose pure vector is Renner `m`-IID in the prototype `ν`. -/
def IsRankOneRennerMIIDIn {m r : ℕ} (ρ : State (TensorPower a (m + r)))
    (ν : PureVector a) : Prop :=
  ∃ ψ : PureVector (TensorPower a (m + r)),
    ψ.IsRennerMIIDIn (a := a) (m := m) (r := r) ν ∧ ρ = ψ.state

end State

/-- A finite source-shaped mixture of IID tensor-power states.

This is the finite expression layer used by de Finetti/post-selection routes:
an index distribution chooses a single-system state, then emits its `n`-fold
tensor power. The actual de Finetti representation theorem is deliberately
not stated here. -/
structure FiniteIidMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] (n : ℕ) where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- The single-system state attached to each mixture index. -/
  states : ι → State a

namespace FiniteIidMixture

variable {n : ℕ} (M : FiniteIidMixture ι a n)

/-- The ensemble of tensor-power states induced by a finite IID mixture. -/
def tensorPowerEnsemble : Ensemble ι (TensorPower a n) where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.states i).tensorPower n

/-- The finite mixture state `∑ᵢ pᵢ ρᵢ^⊗n`. -/
def state : State (TensorPower a n) :=
  M.tensorPowerEnsemble.averageState

/-- The finite IID mixture state is the average state of its tensor-power
ensemble. -/
theorem state_eq_averageState :
    M.state = M.tensorPowerEnsemble.averageState := rfl

@[simp]
theorem tensorPowerEnsemble_probs (i : ι) :
    M.tensorPowerEnsemble.probs i = M.probs i := rfl

@[simp]
theorem tensorPowerEnsemble_states (i : ι) :
    M.tensorPowerEnsemble.states i = (M.states i).tensorPower n := rfl

/-- Matrix form of the finite IID mixture state. -/
@[simp]
theorem state_matrix :
    M.state.matrix =
      ∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix := by
  rfl

/-- A finite IID mixture is fixed by every tensor-factor permutation channel. -/
theorem permutationChannel_apply_state (σ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n σ).applyState M.state = M.state := by
  apply State.ext
  change (permutationChannel (a := a) n σ).map M.state.matrix = M.state.matrix
  rw [M.state_matrix, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (permutationChannel (a := a) n σ).map
      ((M.probs i : ℂ) • ((M.states i).tensorPower n).matrix) =
    (M.probs i : ℂ) • ((M.states i).tensorPower n).matrix
  rw [map_smul]
  have hi := congrArg State.matrix
    (State.permutationChannel_apply_tensorPower (a := a) (M.states i) n σ)
  exact congrArg ((M.probs i : ℂ) • ·) hi

/-- A finite IID mixture state is permutation invariant. -/
theorem state_isPermutationInvariant :
    M.state.IsPermutationInvariant (a := a) := by
  intro σ
  exact M.permutationChannel_apply_state σ

/-- Twirling a finite IID mixture state leaves it unchanged. -/
theorem permutationTwirling_state :
    M.state.permutationTwirling (a := a) = M.state :=
  State.permutationTwirling_apply_of_isPermutationInvariant
    (a := a) M.state_isPermutationInvariant

/-- The one-point IID mixture attached to a single state. -/
def onePoint (ρ : State a) (n : ℕ) : FiniteIidMixture PUnit a n where
  probs := fun _ => 1
  weights_sum := by simp
  states := fun _ => ρ

/-- A one-point IID mixture is exactly the corresponding tensor-power state. -/
theorem onePoint_state (ρ : State a) (n : ℕ) :
    (onePoint (a := a) ρ n).state = ρ.tensorPower n := by
  rw [state]
  exact Ensemble.averageState_of_constant
    ((onePoint (a := a) ρ n).tensorPowerEnsemble) (ρ.tensorPower n)
    (fun i => by cases i; rfl)

end FiniteIidMixture

/-- A finite weighted mixture of pure-state projectors.

This is the finite Lean substitute layer for the source integral over
rank-one projectors in Renner's de Finetti theorem
[Renner2007Symmetry, sub.tex:618-633]. -/
structure FinitePureStateMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- The pure vector attached to each mixture index. -/
  vectors : ι → PureVector a

namespace FinitePureStateMixture

variable (M : FinitePureStateMixture ι a)

/-- The state ensemble induced by a finite pure-state mixture. -/
def toEnsemble : Ensemble ι a where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.vectors i).state

/-- The barycentric state `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`. -/
def state : State a :=
  M.toEnsemble.averageState

/-- Matrix form of the finite pure-state barycenter. -/
@[simp]
theorem state_matrix :
    M.state.matrix = ∑ i, (M.probs i) • (M.vectors i).state.matrix := by
  rfl

/-- View a finite pure-state mixture as a finite IID mixture after taking
one-system pure states as density states. -/
def toFiniteIidMixture (n : ℕ) : FiniteIidMixture ι a n where
  probs := M.probs
  weights_sum := M.weights_sum
  states := fun i => (M.vectors i).state

/-- The tensor-power barycenter generated by this pure-state mixture. -/
def tensorPowerState (n : ℕ) : State (TensorPower a n) :=
  (M.toFiniteIidMixture n).state

/-- Tensor-power pure mixtures are exactly the existing `FiniteIidMixture`
construction applied to the corresponding rank-one states. -/
theorem tensorPower_state_eq_finiteIidMixture_state (n : ℕ) :
    M.tensorPowerState n = (M.toFiniteIidMixture n).state := rfl

/-- Matrix form of the tensor-power barycenter. -/
@[simp]
theorem tensorPowerState_matrix (n : ℕ) :
    (M.tensorPowerState n).matrix =
      ∑ i, (M.probs i) • ((M.vectors i).state.tensorPower n).matrix := by
  rfl

end FinitePureStateMixture

/-- A finite mixture whose pure components satisfy Renner's rank-one
`m`-IID-in-`ν` condition.

The source theorem uses a measure over one-dimensional projectors `ν` and
density operators supported on the span of `m`-IID vectors in `ν`. This finite
wrapper records the rank-one/vector-level component support that the later
Renner approximation theorem can average. -/
structure FiniteRennerMIIDMixture (ι : Type u) (a : Type v) [Fintype ι]
    [Fintype a] [DecidableEq a] (m r : ℕ) where
  /-- Nonnegative weights over the finite mixture index. -/
  probs : ι → ℝ≥0
  /-- The weights form a probability distribution. -/
  weights_sum : (∑ i, probs i) = 1
  /-- Pure components on `a^(m+r)`. -/
  vectors : ι → PureVector (TensorPower a (m + r))
  /-- The single-system pure vector `ν` witnessing the component's `m`-IID part. -/
  bases : ι → PureVector a
  /-- Each component is Renner `m`-IID in its corresponding rank-one projector. -/
  renner_miid : ∀ i, (vectors i).IsRennerMIIDIn (a := a) (m := m) (r := r) (bases i)

namespace FiniteRennerMIIDMixture

variable {m r : ℕ} (M : FiniteRennerMIIDMixture ι a m r)

/-- Forget the Renner support witnesses and retain the finite pure-state
barycenter. -/
def toFinitePureStateMixture :
    FinitePureStateMixture ι (TensorPower a (m + r)) where
  probs := M.probs
  weights_sum := M.weights_sum
  vectors := M.vectors

/-- The finite barycenter of Renner `m`-IID pure components. -/
def state : State (TensorPower a (m + r)) :=
  M.toFinitePureStateMixture.state

/-- Matrix form of the finite Renner `m`-IID barycenter. -/
@[simp]
theorem state_matrix :
    M.state.matrix = ∑ i, (M.probs i) • (M.vectors i).state.matrix := by
  rfl

/-- Each component state satisfies the rank-one Renner `m`-IID wrapper from
the nested partial-trace API. -/
theorem component_isRankOneRennerMIIDIn (i : ι) :
    (M.vectors i).state.IsRankOneRennerMIIDIn (a := a) (m := m) (r := r)
      (M.bases i) := by
  exact ⟨M.vectors i, M.renner_miid i, rfl⟩

end FiniteRennerMIIDMixture

namespace State

variable {n : ℕ}

/-- Normalized trace distance to a finite Renner `m`-IID mixture unfolds to
the matrix-level distance against the explicit finite barycenter. -/
theorem normalizedTraceDistance_finiteRennerMIIDMixture_state_eq
    {m r : ℕ} (ρ : State (TensorPower a (m + r)))
    (M : FiniteRennerMIIDMixture ι a m r) :
    ρ.normalizedTraceDistance M.state =
      QIT.normalizedTraceDistance ρ.matrix
        (∑ i, (M.probs i) • (M.vectors i).state.matrix) := by
  rw [State.normalizedTraceDistance_eq_matrix, M.state_matrix]

private theorem matrix_le_one (ρ : State a) :
    ρ.matrix ≤ 1 := by
  classical
  rw [Matrix.le_iff]
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.1.eigenvectorUnitary
  let D : CMatrix a := Matrix.diagonal fun i => ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)
  have hdiag : ρ.matrix = (U : CMatrix a) * D * star (U : CMatrix a) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.1.spectral_theorem
  have hUstarU : star (U : CMatrix a) * (U : CMatrix a) = 1 := by
    simp [U]
  have heig_sum : ∑ i, ρ.pos.1.eigenvalues i = 1 := by
    have hc : (∑ i, ((ρ.pos.1.eigenvalues i : ℝ) : ℂ)) = 1 := by
      exact ρ.pos.1.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
    exact Complex.ofReal_injective (by simpa using hc)
  have heig_le_one : ∀ i, ρ.pos.1.eigenvalues i ≤ 1 := by
    intro i
    have hnonneg (j : a) : 0 ≤ ρ.pos.1.eigenvalues j :=
      ρ.pos.eigenvalues_nonneg j
    calc ρ.pos.1.eigenvalues i
        ≤ ρ.pos.1.eigenvalues i +
            ∑ j ∈ Finset.univ.erase i, ρ.pos.1.eigenvalues j :=
          le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hnonneg j))
      _ = ∑ j, ρ.pos.1.eigenvalues j := by
          rw [add_comm]
          exact Finset.sum_erase_add (s := Finset.univ)
            (f := fun j => ρ.pos.1.eigenvalues j) (Finset.mem_univ i)
      _ = 1 := heig_sum
  have hsub :
      1 - ρ.matrix = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
    rw [hdiag]
    have hUstar : (U : CMatrix a) * star (U : CMatrix a) = 1 := by
      simp
    calc
      1 - (U : CMatrix a) * D * star (U : CMatrix a) =
          (U : CMatrix a) * 1 * star (U : CMatrix a) -
            (U : CMatrix a) * D * star (U : CMatrix a) := by
            rw [Matrix.mul_one, hUstar]
      _ = (U : CMatrix a) * (1 - D) * star (U : CMatrix a) := by
            noncomm_ring
  have hdiag_sub :
      (1 : CMatrix a) - D =
        Matrix.diagonal fun i => (((1 : ℝ) - ρ.pos.1.eigenvalues i : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  rw [hsub]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe :
    IsUnit (U : CMatrix a))]
  rw [hdiag_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro i
  have hnonneg : 0 ≤ (1 : ℝ) - ρ.pos.1.eigenvalues i := by
    exact sub_nonneg.mpr (heig_le_one i)
  exact_mod_cast hnonneg

private theorem cMatrix_trace_mul_le_of_le {D X Y : CMatrix a}
    (hD : D.PosSemidef) (hXY : X ≤ Y) :
    ((D * X).trace).re ≤ ((D * Y).trace).re := by
  rw [Matrix.le_iff] at hXY
  have hnonneg : 0 ≤ ((D * (Y - X)).trace).re := by
    let S := psdSqrt D
    have hpsd : (S * (Y - X) * S).PosSemidef := by
      have h := hXY.mul_mul_conjTranspose_same S
      rw [psdSqrt_isHermitian D] at h
      exact h
    have htrace_re : 0 ≤ ((S * (Y - X) * S).trace).re :=
      (Matrix.PosSemidef.trace_nonneg hpsd).1
    have hEq : (D * (Y - X)).trace = (S * (Y - X) * S).trace := by
      have hSsq : S * S = D := by
        simpa [S] using psdSqrt_mul_self_of_posSemidef hD
      rw [← hSsq]
      calc
        ((S * S) * (Y - X)).trace = (S * (S * (Y - X))).trace := by
          rw [Matrix.mul_assoc]
        _ = ((S * (Y - X)) * S).trace := by rw [Matrix.trace_mul_comm]
        _ = (S * (Y - X) * S).trace := by rw [Matrix.mul_assoc]
    rwa [hEq]
  have hcalc : ((D * (Y - X)).trace).re =
      ((D * Y).trace).re - ((D * X).trace).re := by
    simp [Matrix.mul_sub, Matrix.trace_sub]
  linarith

/-- The normalized Reynolds/symmetric-subspace reference state.

This is the finite-dimensional post-selection reference supported on the
symmetric tensor-power subspace: its matrix is `P_sym / Tr(P_sym)`. -/
def symmetricProjectionReferenceState [Nonempty a] (n : ℕ) :
    State (TensorPower a n) where
  matrix := ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
    symmetricProjectionMatrix (a := a) n
  pos := by
    exact (symmetricProjectionMatrix_posSemidef (a := a) n).smul
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (TensorPowerProfile a n))))
  trace_eq_one := by
    rw [Matrix.trace_smul, symmetricProjectionMatrix_trace_eq_profile_card]
    change ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ •
        (Fintype.card (TensorPowerProfile a n) : ℂ) = 1)
    rw [Algebra.smul_def]
    norm_num [TensorPowerProfile.card_ne_zero (a := a) n]

@[simp]
theorem symmetricProjectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).matrix =
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
        symmetricProjectionMatrix (a := a) n := rfl

/-- A state is bounded by the symmetric Reynolds projection in the
positive-semidefinite order.

This is the support-shaped hypothesis needed for the finite-dimensional core
of the post-selection domination inequality. It is stronger than mere
permutation invariance: invariant mixed states may still have support outside
the symmetric subspace. -/
def SupportedOnSymmetricSubspace (ρ : State (TensorPower a n)) : Prop :=
  ρ.matrix ≤ symmetricProjectionMatrix (a := a) n

theorem supportedOnSymmetricSubspace_iff (ρ : State (TensorPower a n)) :
    ρ.SupportedOnSymmetricSubspace (a := a) ↔
      ρ.matrix ≤ symmetricProjectionMatrix (a := a) n := by
  rfl

/-- The normalized symmetric projection reference state is supported on the
symmetric tensor-power subspace. -/
theorem symmetricProjectionReferenceState_supportedOnSymmetricSubspace
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).SupportedOnSymmetricSubspace
      (a := a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [Matrix.le_iff]
  have hcard_one : (1 : ℝ) ≤ Fintype.card (TensorPowerProfile a n) := by
    exact_mod_cast Nat.succ_le_of_lt (TensorPowerProfile.card_pos (a := a) n)
  have hscale : 0 ≤ (1 : ℝ) - (Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ := by
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hcard_one)
  convert (symmetricProjectionMatrix_posSemidef (a := a) n).smul hscale using 1
  ext x y
  simp [sub_smul, Matrix.smul_apply]

/-- CKR de Finetti reference state for the finite-dimensional post-selection
route.

The source writes this state as `τ_{H^n}` and identifies it with the
finite-dimensional de Finetti input used by the post-selection theorem.  In
this library it is represented by the already-proved normalized Reynolds
projection `P_sym / Tr(P_sym)`.  This is the source-facing name; it does not
claim the Haar-integral representation as a separate theorem. -/
abbrev deFinettiReferenceState [Nonempty a] (n : ℕ) :
    State (TensorPower a n) :=
  symmetricProjectionReferenceState (a := a) n

@[simp]
theorem deFinettiReferenceState_eq_symmetricProjectionReferenceState
    [Nonempty a] (n : ℕ) :
    deFinettiReferenceState (a := a) n =
      symmetricProjectionReferenceState (a := a) n :=
  rfl

@[simp]
theorem deFinettiReferenceState_matrix [Nonempty a] (n : ℕ) :
    (deFinettiReferenceState (a := a) n).matrix =
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹) •
        symmetricProjectionMatrix (a := a) n :=
  rfl

theorem deFinettiReferenceState_supportedOnSymmetricSubspace
    [Nonempty a] (n : ℕ) :
    (deFinettiReferenceState (a := a) n).SupportedOnSymmetricSubspace
      (a := a) :=
  symmetricProjectionReferenceState_supportedOnSymmetricSubspace (a := a) n

theorem deFinettiReferenceState_trace_eq_one [Nonempty a] (n : ℕ) :
    (deFinettiReferenceState (a := a) n).matrix.trace = 1 :=
  (deFinettiReferenceState (a := a) n).trace_eq_one

theorem deFinettiReferenceState_trace_re_eq_one [Nonempty a] (n : ℕ) :
    ((deFinettiReferenceState (a := a) n).matrix.trace).re = 1 := by
  rw [deFinettiReferenceState_trace_eq_one]
  norm_num

theorem deFinettiReferenceState_profile_count_factor [Nonempty a] (n : ℕ) :
    ((Fintype.card (TensorPowerProfile a n) : ℝ) : ℂ) •
        (deFinettiReferenceState (a := a) n).matrix =
      symmetricProjectionMatrix (a := a) n := by
  change (Fintype.card (TensorPowerProfile a n) : ℂ) •
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ •
        symmetricProjectionMatrix (a := a) n) =
    symmetricProjectionMatrix (a := a) n
  ext x y
  simp [Matrix.smul_apply, smul_eq_mul, TensorPowerProfile.card_ne_zero (a := a) n]

/-- Matrix domination of states in the positive-semidefinite order.

`ρ.MatrixDominatedBy c σ` means `ρ ≤ c σ` at the matrix level. This is the
operator-order expression used by post-selection/de Finetti domination bounds. -/
def MatrixDominatedBy (ρ : State a) (c : ℝ) (σ : State a) : Prop :=
  ρ.matrix ≤ (c : ℂ) • σ.matrix

theorem matrixDominatedBy_iff (ρ σ : State a) (c : ℝ) :
    ρ.MatrixDominatedBy c σ ↔ ρ.matrix ≤ (c : ℂ) • σ.matrix := by
  rfl

/-- Every state is dominated by itself with factor `1`. -/
theorem matrixDominatedBy_refl (ρ : State a) :
    ρ.MatrixDominatedBy 1 ρ := by
  simp [MatrixDominatedBy]

@[simp]
theorem symmetricProjectionReferenceState_matrixDominatedBy_self
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).MatrixDominatedBy 1
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_refl (symmetricProjectionReferenceState (a := a) n)

/-- Equality gives domination with factor `1`. -/
theorem matrixDominatedBy_of_eq {ρ σ : State a} (h : ρ = σ) :
    ρ.MatrixDominatedBy 1 σ := by
  subst h
  exact matrixDominatedBy_refl ρ

/-- Matrix domination is monotone in the scalar factor. -/
theorem matrixDominatedBy_mono_factor {ρ σ : State a} {c d : ℝ}
    (h : ρ.MatrixDominatedBy c σ) (hcd : c ≤ d) :
    ρ.MatrixDominatedBy d σ := by
  dsimp [MatrixDominatedBy] at h ⊢
  exact le_trans h (by
    change (((d : ℂ) • σ.matrix) - ((c : ℂ) • σ.matrix)).PosSemidef
    convert σ.pos.smul (by exact_mod_cast sub_nonneg.mpr hcd) using 1
    ext i j
    simp [sub_smul])

/-- Core post-selection domination: any state already bounded by the symmetric
projection is dominated by the normalized symmetric reference state with factor
equal to the symmetric profile dimension. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    [Nonempty a] {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) := by
  dsimp [MatrixDominatedBy, SupportedOnSymmetricSubspace] at hρ ⊢
  convert hρ using 1
  change (Fintype.card (TensorPowerProfile a n) : ℂ) •
      ((Fintype.card (TensorPowerProfile a n) : ℝ)⁻¹ •
        symmetricProjectionMatrix (a := a) n) =
    symmetricProjectionMatrix (a := a) n
  ext x y
  simp [Matrix.smul_apply, smul_eq_mul, TensorPowerProfile.card_ne_zero (a := a) n]

/-- Polynomial-factor form of the core post-selection domination inequality,
using the profile-count bound `(n+1)^|a|`. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
    [Nonempty a] {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (symmetricProjectionReferenceState (a := a) n) := by
  exact matrixDominatedBy_mono_factor
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)
    (by exact_mod_cast tensorPowerProfile_card_le_pow_succ (a := a) n)

/-- CKR de Finetti reference domination with the exact profile-count factor. -/
theorem matrixDominatedBy_deFinettiReferenceState_profile_count_of_supported
    [Nonempty a] {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy (Fintype.card (TensorPowerProfile a n) : ℝ)
      (deFinettiReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    (a := a) hρ

/-- CKR de Finetti reference domination with the polynomial profile-count
bound `(n+1)^|a|`. -/
theorem matrixDominatedBy_deFinettiReferenceState_pow_succ_of_supported
    [Nonempty a] {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (deFinettiReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
    (a := a) hρ

@[simp]
theorem symmetricProjectionReferenceState_matrixDominatedBy_profile_count
    [Nonempty a] (n : ℕ) :
    (symmetricProjectionReferenceState (a := a) n).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    (a := a)
    (symmetricProjectionReferenceState_supportedOnSymmetricSubspace
      (a := a) n)

/-- Matrix domination composes multiplicatively in the scalar factor. -/
theorem matrixDominatedBy_trans {ρ σ τ : State a} {c d : ℝ}
    (hc : 0 ≤ c) (hρσ : ρ.MatrixDominatedBy c σ)
    (hστ : σ.MatrixDominatedBy d τ) :
    ρ.MatrixDominatedBy (c * d) τ := by
  dsimp [MatrixDominatedBy] at hρσ hστ ⊢
  refine le_trans hρσ ?_
  change (((c * d : ℝ) : ℂ) • τ.matrix - (c : ℂ) • σ.matrix).PosSemidef
  convert hστ.smul hc using 1
  ext i j
  simp [mul_smul, mul_sub]

/-- Matrix domination implies the corresponding trace inequality. -/
theorem matrixDominatedBy_trace_re_le {ρ σ : State a} {c : ℝ}
    (hρσ : ρ.MatrixDominatedBy c σ) :
    ρ.matrix.trace.re ≤ c * σ.matrix.trace.re := by
  dsimp [MatrixDominatedBy] at hρσ
  have hnon : 0 ≤ ((((c : ℂ) • σ.matrix) - ρ.matrix).trace).re :=
    (Matrix.PosSemidef.trace_nonneg hρσ).1
  have htrace : ((((c : ℂ) • σ.matrix) - ρ.matrix).trace).re =
      c * σ.matrix.trace.re - ρ.matrix.trace.re := by
    simp [Matrix.trace_sub, Matrix.trace_smul]
  rw [htrace] at hnon
  linarith

/-- A domination factor between normalized states is necessarily at least
`1`. -/
theorem one_le_factor_of_matrixDominatedBy {ρ σ : State a} {c : ℝ}
    (hρσ : ρ.MatrixDominatedBy c σ) :
    1 ≤ c := by
  have htrace := matrixDominatedBy_trace_re_le hρσ
  have hρtr : ρ.matrix.trace.re = 1 := by
    rw [ρ.trace_eq_one]
    norm_num
  have hσtr : σ.matrix.trace.re = 1 := by
    rw [σ.trace_eq_one]
    norm_num
  rw [hρtr, hσtr, mul_one] at htrace
  exact htrace

/-- Matrix domination by a normalized state gives a normalized trace-distance
bound.  This is the state-level norm expression used by post-selection-style
channel-output estimates: from `ρ ≤ c σ` one obtains
`T(ρ, σ) ≤ c - 1`. -/
theorem normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy
    {ρ σ : State a} {c : ℝ} (hρσ : ρ.MatrixDominatedBy c σ) :
    ρ.normalizedTraceDistance σ ≤ c - 1 := by
  let H : CMatrix a := ρ.matrix - σ.matrix
  have hH : H.IsHermitian := ρ.pos.isHermitian.sub σ.pos.isHermitian
  let P : CMatrix a := positiveSpectralProjector H hH
  have hPpos : P.PosSemidef := positiveSpectralProjector_posSemidef H hH
  have hPle : P ≤ 1 := positiveSpectralProjector_le_one H hH
  have hdiff_le : H ≤ ((c - 1 : ℝ) : ℂ) • σ.matrix := by
    dsimp [H]
    have hρσ_le : ρ.matrix ≤ (c : ℂ) • σ.matrix := by
      simpa [MatrixDominatedBy] using hρσ
    rw [Matrix.le_iff] at hρσ_le ⊢
    convert hρσ_le using 1
    ext i j
    simp [Matrix.smul_apply]
    ring
  have hscore :
      ((P * H).trace).re = (H⁺).trace.re := by
    rw [Matrix.trace_mul_comm P H]
    exact positiveSpectralProjector_score_eq_posPart_trace H hH
  have htrace_le :
      ((P * H).trace).re ≤ ((P * (((c - 1 : ℝ) : ℂ) • σ.matrix)).trace).re :=
    cMatrix_trace_mul_le_of_le hPpos hdiff_le
  have hσP_le_one : ((P * σ.matrix).trace).re ≤ 1 := by
    have h := cMatrix_trace_mul_le_of_le σ.pos hPle
    have hcomm : ((P * σ.matrix).trace).re = ((σ.matrix * P).trace).re := by
      rw [Matrix.trace_mul_comm P σ.matrix]
    have hone : ((σ.matrix * (1 : CMatrix a)).trace).re = 1 := by
      rw [Matrix.mul_one, σ.trace_eq_one]
      norm_num
    calc
      ((P * σ.matrix).trace).re = ((σ.matrix * P).trace).re := hcomm
      _ ≤ ((σ.matrix * (1 : CMatrix a)).trace).re := h
      _ = 1 := hone
  have hc_nonneg : 0 ≤ c - 1 := sub_nonneg.mpr (one_le_factor_of_matrixDominatedBy hρσ)
  have hscaled :
      ((P * (((c - 1 : ℝ) : ℂ) • σ.matrix)).trace).re =
        (c - 1) * ((P * σ.matrix).trace).re := by
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp
  have hscaled_le :
      ((P * (((c - 1 : ℝ) : ℂ) • σ.matrix)).trace).re ≤ c - 1 := by
    rw [hscaled]
    have hmul := mul_le_mul_of_nonneg_left hσP_le_one hc_nonneg
    simpa [mul_one] using hmul
  rw [State.normalizedTraceDistance_eq_posPart_trace]
  calc
    ((ρ.matrix - σ.matrix)⁺).trace.re = (H⁺).trace.re := by rfl
    _ = ((P * H).trace).re := hscore.symm
    _ ≤ ((P * (((c - 1 : ℝ) : ℂ) • σ.matrix)).trace).re := htrace_le
    _ ≤ c - 1 := hscaled_le

/-- Channel-output trace-distance bound associated to a chosen reference
output state. This is the trace-norm expression layer parallel to the matrix
domination post-selection bounds. The library currently has no diamond-norm
definition, so the durable channel-level statement is phrased for every finite
output state produced by a channel. -/
def ChannelOutputTraceDistanceBound {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel a b) (ρ σ : State a) (ε : ℝ) : Prop :=
  (Φ.applyState ρ).normalizedTraceDistance (Φ.applyState σ) ≤ ε

/-- Matrix domination is preserved by applying the same channel to both
states. -/
theorem matrixDominatedBy_applyChannel {b : Type w} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {c : ℝ} (Φ : Channel a b)
    (hρσ : ρ.MatrixDominatedBy c σ) :
    (Φ.applyState ρ).MatrixDominatedBy c (Φ.applyState σ) := by
  dsimp [MatrixDominatedBy] at hρσ
  change (((c : ℂ) • (Φ.applyState σ).matrix) - (Φ.applyState ρ).matrix).PosSemidef
  change (((c : ℂ) • Φ.map σ.matrix) - Φ.map ρ.matrix).PosSemidef
  have hpos := Φ.mapsPositive (((c : ℂ) • σ.matrix) - ρ.matrix) hρσ
  convert hpos using 1
  rw [map_sub, map_smul]

/-- Matrix domination gives a channel-output normalized trace-distance bound
after applying the same channel to both states. -/
theorem channelOutputTraceDistanceBound_of_matrixDominatedBy
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ σ : State a} {c : ℝ} (Φ : Channel a b)
    (hρσ : ρ.MatrixDominatedBy c σ) :
    ChannelOutputTraceDistanceBound Φ ρ σ (c - 1) :=
  normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy
    (matrixDominatedBy_applyChannel Φ hρσ)

/-- Finite-reference channel-distance expression for a pair of channels.

This is the operational finite-ancilla layer underlying diamond-distance
statements: every joint input state on `A × R` is tested after applying either
channel to `A` and the identity channel to `R`. -/
def AncillaChannelTraceDistanceBound
    {b : Type w} [Fintype b] [DecidableEq b]
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel a b) (ε : ℝ) : Prop :=
  ∀ ω : State (Prod a r),
    ((Φ.prod (Channel.idChannel r)).applyState ω).normalizedTraceDistance
      ((Ψ.prod (Channel.idChannel r)).applyState ω) ≤ ε

/-- Diamond-distance-shaped expression for a pair of finite-dimensional
channels, stated as a uniform bound over all finite reference systems.

This is an expression layer, not yet a separate numeric norm API. -/
def DiamondTraceDistanceBound
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ Ψ : Channel a b) (ε : ℝ) : Prop :=
  ∀ {r : Type x} [Fintype r] [DecidableEq r],
    AncillaChannelTraceDistanceBound (a := a) (b := b) (r := r) Φ Ψ ε

/-- A uniform matrix-domination bound on every finite-reference channel output
implies the corresponding diamond-distance-shaped trace-distance bound. -/
theorem diamondTraceDistanceBound_of_ancilla_matrixDominatedBy
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : Channel a b} {c : ℝ}
    (h : ∀ {r : Type x} [Fintype r] [DecidableEq r]
      (ω : State (Prod a r)),
        ((Φ.prod (Channel.idChannel r)).applyState ω).MatrixDominatedBy c
          ((Ψ.prod (Channel.idChannel r)).applyState ω)) :
    ∀ {r : Type x} [Fintype r] [DecidableEq r],
      AncillaChannelTraceDistanceBound (a := a) (b := b) (r := r) Φ Ψ (c - 1) := by
  intro r _ _ ω
  exact normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy (h (r := r) ω)

/-- The de-Finetti/post-selection input-reference expression layer feeds the
numeric source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_inputReferenceBound [Nonempty a]
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : AncillaChannelTraceDistanceBound (a := a) (b := b) (r := a) Φ Ψ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε :=
  Channel.diamondTraceDistance_le_of_ancillaBound
    (a := a) (b := b) (Φ := Φ) (Ψ := Ψ) (ε := ε) h

/-- A universe-specialized de-Finetti/post-selection finite-ancilla expression
layer feeds the numeric source-shaped diamond trace distance. -/
theorem diamondTraceDistance_le_of_DiamondTraceDistanceBound [Nonempty a]
    {b : Type w} [Fintype b] [DecidableEq b]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : DiamondTraceDistanceBound.{v, w, v} (a := a) (b := b) Φ Ψ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε :=
  diamondTraceDistance_le_of_inputReferenceBound
    (a := a) (b := b) (Φ := Φ) (Ψ := Ψ) (ε := ε) (h (r := a))

/-- Applying a channel to a state supported in the symmetric tensor-power
subspace gives the channel-output form of the core post-selection domination
bound with the exact profile-count factor. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)

/-- Polynomial-factor channel-output form of the core post-selection
domination bound. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Channel-output CKR de Finetti reference domination with the exact
profile-count factor. -/
theorem matrixDominatedBy_applyChannel_deFinettiReferenceState_profile_count_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (deFinettiReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_deFinettiReferenceState_profile_count_of_supported
      (a := a) hρ)

/-- Channel-output CKR de Finetti reference domination with the polynomial
profile-count bound. -/
theorem matrixDominatedBy_applyChannel_deFinettiReferenceState_pow_succ_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (deFinettiReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (matrixDominatedBy_deFinettiReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Polynomial-factor trace-distance form of the state-level post-selection
bound for a supported symmetric input. -/
theorem stateLevelPostSelectionTraceDistanceBound_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (symmetricProjectionReferenceState (a := a) n)
      (((n + 1) ^ Fintype.card a : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Polynomial-factor trace-distance form of the state-level post-selection
bound, using the source-facing CKR de Finetti reference state. -/
theorem stateLevelPostSelectionTraceDistanceBound_deFinettiReferenceState_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (deFinettiReferenceState (a := a) n)
      (((n + 1) ^ Fintype.card a : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_deFinettiReferenceState_pow_succ_of_supported
      (a := a) hρ)

/-- Exact profile-count trace-distance form of the state-level post-selection
bound for a supported symmetric input. -/
theorem stateLevelPostSelectionTraceDistanceBound_profile_count_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (symmetricProjectionReferenceState (a := a) n)
      ((Fintype.card (TensorPowerProfile a n) : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_symmetricProjectionReferenceState_of_supported
      (a := a) hρ)

/-- Exact profile-count trace-distance form of the state-level post-selection
bound, using the source-facing CKR de Finetti reference state. -/
theorem stateLevelPostSelectionTraceDistanceBound_deFinettiReferenceState_profile_count_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ChannelOutputTraceDistanceBound Φ ρ
      (deFinettiReferenceState (a := a) n)
      ((Fintype.card (TensorPowerProfile a n) : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (matrixDominatedBy_deFinettiReferenceState_profile_count_of_supported
      (a := a) hρ)

@[simp]
theorem symmetricProjectionReferenceState_applyChannel_matrixDominatedBy_self
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).MatrixDominatedBy 1
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_refl
    (Φ.applyState (symmetricProjectionReferenceState (a := a) n))

@[simp]
theorem symmetricProjectionReferenceState_applyChannel_matrixDominatedBy_profile_count
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (symmetricProjectionReferenceState_matrixDominatedBy_profile_count
      (a := a) n)

/-- State-level post-selection domination wrapper with the polynomial
profile-count bound. If the input state is supported on the symmetric
subspace, then every channel output is dominated by the output of the
normalized symmetric projection reference state. -/
theorem stateLevelPostSelectionBound_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_supported
    (a := a) Φ hρ

/-- Exact profile-count version of `stateLevelPostSelectionBound_of_supported`. -/
theorem stateLevelPostSelectionBound_profile_count_of_supported
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    {ρ : State (TensorPower a n)} (Φ : Channel (TensorPower a n) b)
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    (Φ.applyState ρ).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_supported
    (a := a) Φ hρ

/-- Matrix domination is preserved when both states are acted on by the same
tensor-factor permutation channel. -/
theorem matrixDominatedBy_apply_permutationChannel
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hρτ : ρ.MatrixDominatedBy c τ) (σ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n σ).applyState ρ).MatrixDominatedBy c
      ((permutationChannel (a := a) n σ).applyState τ) :=
  matrixDominatedBy_applyChannel (permutationChannel (a := a) n σ) hρτ

/-- Applying a tensor-factor permutation channel to the left side preserves
domination by a permutation-invariant target. -/
theorem matrixDominatedBy_apply_permutationChannel_of_target_invariant
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hτ : τ.IsPermutationInvariant (a := a)) (hρτ : ρ.MatrixDominatedBy c τ)
    (σ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n σ).applyState ρ).MatrixDominatedBy c τ := by
  dsimp [MatrixDominatedBy] at hρτ
  change (((c : ℂ) • τ.matrix) -
    ((permutationChannel (a := a) n σ).applyState ρ).matrix).PosSemidef
  change (((c : ℂ) • τ.matrix) -
    (permutationChannel (a := a) n σ).map ρ.matrix).PosSemidef
  have hpos := (permutationChannel (a := a) n σ).mapsPositive
    (((c : ℂ) • τ.matrix) - ρ.matrix) hρτ
  convert hpos using 1
  rw [map_sub, map_smul]
  have hτmatrix := congrArg State.matrix (hτ σ)
  change (permutationChannel (a := a) n σ).map τ.matrix = τ.matrix at hτmatrix
  rw [hτmatrix]

/-- Permutation twirling the left side preserves domination by a
permutation-invariant target. -/
theorem permutationTwirling_matrixDominatedBy_of_target_invariant
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hτ : τ.IsPermutationInvariant (a := a)) (hρτ : ρ.MatrixDominatedBy c τ) :
    ρ.permutationTwirling.MatrixDominatedBy c τ := by
  dsimp [MatrixDominatedBy]
  change (((c : ℂ) • τ.matrix) - ρ.permutationTwirling.matrix).PosSemidef
  let α : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (((c : ℂ) • τ.matrix) -
        ((permutationChannel (a := a) n σ).applyState ρ).matrix).PosSemidef := by
    intro σ
    exact matrixDominatedBy_apply_permutationChannel_of_target_invariant
      (a := a) hτ hρτ σ
  have hsum : (∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • τ.matrix) -
        ((permutationChannel (a := a) n σ).applyState ρ).matrix)).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun σ _ =>
      (hterm σ).smul (inv_nonneg.mpr
        (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n)))))
  convert hsum using 1
  change ((c : ℂ) • τ.matrix) -
      (α • ∑ σ : Equiv.Perm (Fin n),
        ((permutationChannel (a := a) n σ).applyState ρ).matrix) =
    ∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • τ.matrix) -
        ((permutationChannel (a := a) n σ).applyState ρ).matrix)
  have hcoeff :
      (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.matrix)) =
        ((c : ℂ) • τ.matrix) := by
    rw [← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hα : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * α = 1 := by
      dsimp [α]
      field_simp [Nat.cast_ne_zero.mpr
        (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]
    rw [hα, one_smul]
  calc
    ((c : ℂ) • τ.matrix) -
        (α • ∑ σ : Equiv.Perm (Fin n),
          ((permutationChannel (a := a) n σ).applyState ρ).matrix)
        = (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.matrix)) -
          (α • ∑ σ : Equiv.Perm (Fin n),
            ((permutationChannel (a := a) n σ).applyState ρ).matrix) := by
            rw [hcoeff]
    _ = (∑ _σ : Equiv.Perm (Fin n), α • ((c : ℂ) • τ.matrix)) -
          (∑ σ : Equiv.Perm (Fin n), α •
            ((permutationChannel (a := a) n σ).applyState ρ).matrix) := by
            rw [Finset.smul_sum]
    _ = ∑ σ : Equiv.Perm (Fin n), (α • ((c : ℂ) • τ.matrix) -
          α • ((permutationChannel (a := a) n σ).applyState ρ).matrix) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ σ : Equiv.Perm (Fin n), α •
          (((c : ℂ) • τ.matrix) -
            ((permutationChannel (a := a) n σ).applyState ρ).matrix) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [smul_sub]

/-- Permutation twirling preserves matrix domination when applied to both
sides. -/
theorem permutationTwirling_matrixDominatedBy
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hρτ : ρ.MatrixDominatedBy c τ) :
    ρ.permutationTwirling.MatrixDominatedBy c τ.permutationTwirling := by
  dsimp [MatrixDominatedBy]
  change (((c : ℂ) • τ.permutationTwirling.matrix) -
    ρ.permutationTwirling.matrix).PosSemidef
  let α : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (((c : ℂ) • ((permutationChannel (a := a) n σ).applyState τ).matrix) -
        ((permutationChannel (a := a) n σ).applyState ρ).matrix).PosSemidef := by
    intro σ
    exact matrixDominatedBy_apply_permutationChannel (a := a) hρτ σ
  have hsum : (∑ σ : Equiv.Perm (Fin n), α •
      (((c : ℂ) • ((permutationChannel (a := a) n σ).applyState τ).matrix) -
        ((permutationChannel (a := a) n σ).applyState ρ).matrix)).PosSemidef := by
    exact Matrix.posSemidef_sum Finset.univ fun σ _ =>
      (hterm σ).smul (inv_nonneg.mpr
        (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n)))))
  convert hsum using 1
  ext x y
  simp only [State.permutationTwirling, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.sub_apply, smul_sub, Finset.sum_sub_distrib]
  simp [Finset.mul_sum, mul_left_comm, α]

/-- If an invariant state's twirling is dominated by a target, then the state
itself is dominated by that target. -/
theorem matrixDominatedBy_of_permutationTwirling_left
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a))
    (h : ρ.permutationTwirling.MatrixDominatedBy c τ) :
    ρ.MatrixDominatedBy c τ := by
  rwa [State.permutationTwirling_apply_of_isPermutationInvariant (a := a) hρ] at h

/-- For a permutation-invariant state, domination can be checked after
twirling the left side. -/
theorem matrixDominatedBy_twirling_left_iff_of_invariant
    {ρ τ : State (TensorPower a n)} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.permutationTwirling.MatrixDominatedBy c τ ↔ ρ.MatrixDominatedBy c τ := by
  rw [State.permutationTwirling_apply_of_isPermutationInvariant (a := a) hρ]

/-- A state is dominated by a specified finite IID mixture if its matrix is
bounded by a constant multiple of the mixture state's matrix. -/
def IsDominatedByFiniteIidMixture (ρ : State (TensorPower a n)) (c : ℝ)
    (M : FiniteIidMixture ι a n) : Prop :=
  ρ.MatrixDominatedBy c M.state

theorem isDominatedByFiniteIidMixture_iff (ρ : State (TensorPower a n)) (c : ℝ)
    (M : FiniteIidMixture ι a n) :
    ρ.IsDominatedByFiniteIidMixture c M ↔
      ρ.matrix ≤ (c : ℂ) • M.state.matrix := by
  rfl

/-- Existence of some finite IID mixture dominating a tensor-power state.

This is the de Finetti representation entrypoint shape. A full de Finetti
theorem would prove this predicate, with a source-specific factor, for the
appropriate class of symmetric states. -/
def HasFiniteIidDomination (ρ : State (TensorPower a n)) (c : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ρ.IsDominatedByFiniteIidMixture c M

/-- Existence of some finite IID mixture approximating a tensor-power state in
normalized trace distance. -/
def HasFiniteIidMixtureApproximation (ρ : State (TensorPower a n)) (ε : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ρ.normalizedTraceDistance M.state ≤ ε

/-- Existence of a finite IID mixture whose channel image approximates the
channel image of a tensor-power state in normalized trace distance. -/
def HasFiniteIidChannelOutputApproximation
    {b : Type w} [Fintype b] [DecidableEq b]
    (ρ : State (TensorPower a n)) (Φ : Channel (TensorPower a n) b)
    (ε : ℝ) : Prop :=
  ∃ M : FiniteIidMixture ι a n, ChannelOutputTraceDistanceBound Φ ρ M.state ε

/-- A packaged finite-IID-mixture domination witness for a tensor-power state.

This is an expression layer for de Finetti/post-selection routes: it packages a
finite IID mixture together with the hard matrix-domination proof. It does not
assert that every symmetric state has such a witness. -/
structure FiniteIidDomination (ρ : State (TensorPower a n)) (c : ℝ) where
  /-- The finite IID mixture that serves as the reference state. -/
  mixture : FiniteIidMixture ι a n
  /-- The dominated state is bounded by the mixture at matrix level. -/
  domination : ρ.IsDominatedByFiniteIidMixture c mixture

namespace FiniteIidDomination

/-- A finite-IID domination witness gives the channel-output matrix domination
bound for any finite output channel. -/
theorem applyChannel_matrixDominatedBy
    {ρ : State (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState ρ).MatrixDominatedBy c (Φ.applyState W.mixture.state) :=
  matrixDominatedBy_applyChannel Φ W.domination

/-- A finite-IID domination witness gives a channel-output normalized
trace-distance bound for any finite output channel. -/
theorem applyChannel_traceDistanceBound
    {ρ : State (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ ρ W.mixture.state (c - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ W.domination

end FiniteIidDomination

/-- A packaged finite-IID domination witness gives the existential de Finetti
domination entrypoint. -/
theorem hasFiniteIidDomination_of_witness
    {ρ : State (TensorPower a n)} {c : ℝ}
    (W : ρ.FiniteIidDomination (ι := ι) c) :
    ρ.HasFiniteIidDomination (ι := ι) c := by
  exact ⟨W.mixture, W.domination⟩

/-- Tensor-power states have the one-point finite-IID domination witness. -/
def tensorPower_finiteIidDomination_onePoint (ρ : State a) (n : ℕ) :
    (ρ.tensorPower n).FiniteIidDomination (ι := PUnit) 1 where
  mixture := FiniteIidMixture.onePoint (a := a) ρ n
  domination := by
    exact matrixDominatedBy_of_eq
      (FiniteIidMixture.onePoint_state (a := a) ρ n).symm

/-- Finite-IID domination implies finite-IID approximation in normalized trace
distance with loss `c - 1`. -/
theorem hasFiniteIidMixtureApproximation_of_hasFiniteIidDomination
    {ρ : State (TensorPower a n)} {c : ℝ}
    (hρ : ρ.HasFiniteIidDomination (ι := ι) c) :
    ρ.HasFiniteIidMixtureApproximation (ι := ι) (c - 1) := by
  rcases hρ with ⟨M, hρM⟩
  exact ⟨M, normalizedTraceDistance_le_factor_sub_one_of_matrixDominatedBy hρM⟩

/-- Finite-IID domination implies a finite-IID channel-output approximation
after applying any finite output channel. -/
theorem hasFiniteIidChannelOutputApproximation_of_hasFiniteIidDomination
    {ρ : State (TensorPower a n)} {c : ℝ}
    (hρ : ρ.HasFiniteIidDomination (ι := ι) c)
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    ρ.HasFiniteIidChannelOutputApproximation (ι := ι) Φ (c - 1) := by
  rcases hρ with ⟨M, hρM⟩
  exact ⟨M, channelOutputTraceDistanceBound_of_matrixDominatedBy Φ hρM⟩

/-- Source-shaped route predicate for proving finite-IID domination of
symmetric tensor-power states.

This is deliberately a predicate: the full de Finetti representation theorem is
the future hard proof that supplies this route for the desired factor. -/
def SymmetricFiniteIidDominationRoute (ι : Type u) (a : Type v)
    [Fintype ι] [Fintype a] [DecidableEq a] (n : ℕ) (c : ℝ) : Prop :=
  ∀ ρ : State (TensorPower a n),
    ρ.SupportedOnSymmetricSubspace (a := a) →
      ρ.HasFiniteIidDomination (ι := ι) c

namespace SymmetricFiniteIidDominationRoute

/-- A symmetric finite-IID domination route gives the corresponding trace-
distance approximation statement for every supported state. -/
theorem toApproximation {n : ℕ} {c : ℝ}
    (route : SymmetricFiniteIidDominationRoute ι a n c)
    {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a)) :
    ρ.HasFiniteIidMixtureApproximation (ι := ι) (c - 1) :=
  State.hasFiniteIidMixtureApproximation_of_hasFiniteIidDomination (route ρ hρ)

/-- A symmetric finite-IID domination route gives a finite-IID approximation
after applying any finite output channel. -/
theorem toChannelOutputApproximation {n : ℕ} {c : ℝ}
    (route : SymmetricFiniteIidDominationRoute ι a n c)
    {ρ : State (TensorPower a n)}
    (hρ : ρ.SupportedOnSymmetricSubspace (a := a))
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    ρ.HasFiniteIidChannelOutputApproximation (ι := ι) Φ (c - 1) :=
  State.hasFiniteIidChannelOutputApproximation_of_hasFiniteIidDomination (route ρ hρ) Φ

end SymmetricFiniteIidDominationRoute

/-- Domination by a specified finite IID mixture is monotone in the scalar
factor. -/
theorem isDominatedByFiniteIidMixture_mono_factor {ρ : State (TensorPower a n)}
    {M : FiniteIidMixture ι a n} {c d : ℝ}
    (h : ρ.IsDominatedByFiniteIidMixture c M) (hcd : c ≤ d) :
    ρ.IsDominatedByFiniteIidMixture d M :=
  matrixDominatedBy_mono_factor h hcd

/-- Domination by a finite IID mixture composes with matrix domination of that
mixture state. -/
theorem isDominatedByFiniteIidMixture_of_matrixDominatedBy_trans
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {τ : State (TensorPower a n)} {c d : ℝ}
    (hc : 0 ≤ c) (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMτ : M.state.MatrixDominatedBy d τ) :
    ρ.MatrixDominatedBy (c * d) τ :=
  matrixDominatedBy_trans hc hρM hMτ

/-- Applying a channel to a state dominated by a finite IID mixture preserves
the domination relation at the matrix level. -/
theorem isDominatedByFiniteIidMixture_applyChannel
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (Φ : Channel (TensorPower a n) b)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M) :
    (Φ.applyState ρ).MatrixDominatedBy c (Φ.applyState M.state) :=
  matrixDominatedBy_applyChannel Φ hρM

/-- Applying a channel to a state dominated by a finite IID mixture and then
bounding the image mixture by a target state gives a composed domination
bound. -/
theorem isDominatedByFiniteIidMixture_applyChannel_trans
    {b : Type w} [Fintype b] [DecidableEq b]
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {τ : State b} {c d : ℝ}
    (Φ : Channel (TensorPower a n) b) (hc : 0 ≤ c)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMτ : (Φ.applyState M.state).MatrixDominatedBy d τ) :
    (Φ.applyState ρ).MatrixDominatedBy (c * d) τ :=
  matrixDominatedBy_trans hc
    (isDominatedByFiniteIidMixture_applyChannel Φ hρM) hMτ

/-- Applying a channel to a state dominated by a finite IID mixture and then
bounding the image mixture by an output finite IID mixture gives a composed
finite-mixture domination bound. -/
theorem isDominatedByFiniteIidMixture_applyChannel_trans_mixture
    {κ : Type x} {b : Type w} [Fintype κ] [Fintype b] [DecidableEq b]
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n}
    {N : FiniteIidMixture κ b n} {c d : ℝ}
    (Φ : Channel (TensorPower a n) (TensorPower b n)) (hc : 0 ≤ c)
    (hρM : ρ.IsDominatedByFiniteIidMixture c M)
    (hMN : (Φ.applyState M.state).IsDominatedByFiniteIidMixture d N) :
    (Φ.applyState ρ).IsDominatedByFiniteIidMixture (c * d) N :=
  isDominatedByFiniteIidMixture_applyChannel_trans Φ hc hρM hMN

/-- Permutation twirling preserves domination by a finite IID mixture. -/
theorem permutationTwirling_isDominatedByFiniteIidMixture
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρM : ρ.IsDominatedByFiniteIidMixture c M) :
    ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M :=
  permutationTwirling_matrixDominatedBy_of_target_invariant
    M.state_isPermutationInvariant hρM

/-- If an invariant state's twirling is dominated by a finite IID mixture, then
the state itself is dominated by that mixture. -/
theorem isDominatedByFiniteIidMixture_of_permutationTwirling_left
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a))
    (h : ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M) :
    ρ.IsDominatedByFiniteIidMixture c M :=
  matrixDominatedBy_of_permutationTwirling_left hρ h

/-- For a permutation-invariant state, finite-IID-mixture domination can be
checked after twirling the state. -/
theorem isDominatedByFiniteIidMixture_twirling_iff_of_invariant
    {ρ : State (TensorPower a n)} {M : FiniteIidMixture ι a n} {c : ℝ}
    (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.permutationTwirling.IsDominatedByFiniteIidMixture c M ↔
      ρ.IsDominatedByFiniteIidMixture c M :=
  matrixDominatedBy_twirling_left_iff_of_invariant hρ

/-- A tensor-power state is dominated with factor `1` by the one-point IID
mixture concentrated on the underlying state. -/
theorem tensorPower_isDominatedBy_onePoint (ρ : State a) (n : ℕ) :
    (ρ.tensorPower n).IsDominatedByFiniteIidMixture 1
      (FiniteIidMixture.onePoint (a := a) ρ n) := by
  exact matrixDominatedBy_of_eq
    (FiniteIidMixture.onePoint_state (a := a) ρ n).symm

/-- The one-point IID domination of a tensor-power state can be enlarged to any
factor at least `1`. -/
theorem tensorPower_isDominatedBy_onePoint_mono_factor (ρ : State a) (n : ℕ)
    {c : ℝ} (hc : 1 ≤ c) :
    (ρ.tensorPower n).IsDominatedByFiniteIidMixture c
      (FiniteIidMixture.onePoint (a := a) ρ n) :=
  isDominatedByFiniteIidMixture_mono_factor
    (tensorPower_isDominatedBy_onePoint (a := a) ρ n) hc

end State

export State (deFinettiReferenceState
  deFinettiReferenceState_eq_symmetricProjectionReferenceState
  deFinettiReferenceState_matrix
  deFinettiReferenceState_supportedOnSymmetricSubspace
  deFinettiReferenceState_trace_eq_one
  deFinettiReferenceState_trace_re_eq_one
  deFinettiReferenceState_profile_count_factor)

/-- CKR post-selection reference state on `H^n × H^n`.

The source theorem evaluates `Δ ⊗ id` on a purification/reference extension of
`τ_{H^n}`.  This finite-dimensional source-facing input is represented as the
de Finetti reference state on `(H × H)^n`, transported across the standard
identification `(H × H)^n ≃ H^n × H^n`. -/
abbrev postSelectionReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n) (TensorPower a n)) :=
  (deFinettiReferenceState (a := Prod a a) n).reindex
    (tensorPowerProdEquiv a a n)

@[simp]
theorem postSelectionReferenceState_matrix [Nonempty a] (n : ℕ) :
    (postSelectionReferenceState (a := a) n).matrix =
      (deFinettiReferenceState (a := Prod a a) n).matrix.submatrix
        (tensorPowerProdEquiv a a n).symm
        (tensorPowerProdEquiv a a n).symm :=
  rfl

theorem postSelectionReferenceState_trace_eq_one [Nonempty a] (n : ℕ) :
    (postSelectionReferenceState (a := a) n).matrix.trace = 1 :=
  (postSelectionReferenceState (a := a) n).trace_eq_one

/-- Entrywise action of a tensor-factor permutation on the left input register,
with the reference register left unchanged. -/
theorem permutationChannel_prod_id_map_apply {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (TensorPower a n) r))
    (x y : Prod (TensorPower a n) r) :
    (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) x y =
      X (permEquiv (a := a) n π x.1, x.2)
        (permEquiv (a := a) n π y.1, y.2) := by
  change MatrixMap.kron (permutationChannel (a := a) n π).map
    (Channel.idChannel r).map X x y = _
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [permutationChannel_map_apply]

/-- Partial trace over the reference register commutes with a tensor-factor
permutation on the input register. -/
theorem partialTraceB_permutation_prod_id_map {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (TensorPower a n) r)) :
    partialTraceB (a := TensorPower a n) (b := r)
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) =
      (permutationChannel (a := a) n π).map
        (partialTraceB (a := TensorPower a n) (b := r) X) := by
  ext x y
  simp only [partialTraceB]
  rw [permutationChannel_map_apply]
  refine Finset.sum_congr rfl fun rr _ => ?_
  rw [permutationChannel_prod_id_map_apply]

namespace State

/-- Average an input-reference state over permutations of the input tensor
factors, leaving the reference register unchanged. -/
def inputPermutationTwirling {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    State (Prod (TensorPower a n) r) where
  matrix := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
    ∑ π : Equiv.Perm (Fin n),
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
  pos := by
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n))))
    have hcC : 0 ≤ (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hcR
    exact (Matrix.posSemidef_sum Finset.univ fun π _ =>
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).pos).smul hcC
  trace_eq_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum]
    calc
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          ∑ π : Equiv.Perm (Fin n),
            ((((permutationChannel (a := a) n π).prod
              (Channel.idChannel r)).applyState ω).matrix).trace) =
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
            (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := by
            simp [State.trace_eq_one, Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            norm_num [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
              Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

/-- Input permutation twirling is invariant under further input permutations. -/
theorem inputPermutationTwirling_apply_permutation {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) (τ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n τ).prod (Channel.idChannel r)).applyState
        (ω.inputPermutationTwirling (a := a) (r := r)) =
      ω.inputPermutationTwirling (a := a) (r := r) := by
  apply State.ext
  ext x y
  dsimp [inputPermutationTwirling]
  simp only [Channel.applyState]
  change MatrixMap.kron (permutationChannel (a := a) n τ).map (Channel.idChannel r).map
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y =
    ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y
  rw [map_smul, map_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
      invFun := fun σ => σ * τ⁻¹,
      left_inv := by intro σ; simp [mul_assoc],
      right_inv := by intro σ; simp [mul_assoc] }
    (fun σ => (MatrixMap.kron (permutationChannel (a := a) n τ).map
      (Channel.idChannel r).map
      (((permutationChannel (a := a) n σ).prod (Channel.idChannel r)).applyState ω).matrix) x y)
    (fun σ => (((permutationChannel (a := a) n σ).prod
      (Channel.idChannel r)).applyState ω).matrix x y) ?_
  intro σ
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    simp only [Channel.applyState]
    rw [MatrixMap.kron_idChannel_apply_slice]
    rw [permutationChannel_map_apply]
    simp only [permutationChannel_prod_id_map_apply]
    change ω.matrix (σ • (τ • xA), xr) (σ • (τ • yA), yr) =
      ω.matrix ((σ * τ) • xA, xr) ((σ * τ) • yA, yr)
    rw [← mul_smul, ← mul_smul]

/-- The input marginal of an input-permutation-twirled state is permutation
invariant. -/
theorem inputPermutationTwirling_marginalA_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationTwirling (a := a) (r := r)).marginalA.IsPermutationInvariant
      (a := a) := by
  intro τ
  apply State.ext
  have hwhole := inputPermutationTwirling_apply_permutation (a := a) (r := r) ω τ
  have hm := congrArg
    (fun ρ : State (Prod (TensorPower a n) r) => ρ.marginalA.matrix) hwhole
  change partialTraceB
      (((permutationChannel (a := a) n τ).prod (Channel.idChannel r)).map
        (ω.inputPermutationTwirling (a := a) (r := r)).matrix) =
    (ω.inputPermutationTwirling (a := a) (r := r)).marginalA.matrix at hm
  rw [partialTraceB_permutation_prod_id_map] at hm
  exact hm

/-- Reindex the canonical purification of an input-reference state into
input-first form, with the original reference and the purifying environment
bundled as the new reference register. -/
def extensionPurificationInputEquiv {r : Type w} {n : ℕ} :
    Equiv (Prod (Prod (TensorPower a n) r) (Prod (TensorPower a n) r))
      (Prod (TensorPower a n) (Prod r (Prod (TensorPower a n) r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xa xrE => cases xrE; rfl

/-- Canonical pure extension of a mixed input-reference state, oriented with
the channel input as the first factor. -/
def inputReferenceCanonicalExtension {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    PureVector (Prod (TensorPower a n) (Prod r (Prod (TensorPower a n) r))) :=
  ω.canonicalPurification.reindex
    (extensionPurificationInputEquiv (a := a) (r := r) (n := n))

/-- Output-side counterpart of `extensionPurificationInputEquiv` after a
channel has acted on the input tensor power. -/
def extensionPurificationOutputEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv (Prod (Prod (TensorPower a n) r) (Prod b r))
      (Prod b (Prod r (Prod (TensorPower a n) r))) where
  toFun x := (x.2.1, (x.2.2, x.1))
  invFun x := (x.2.2, (x.1, x.2.1))
  left_inv := by intro x; cases x with | mk e t => cases e; cases t; rfl
  right_inv := by intro x; cases x with | mk xb xrE => cases xrE; rfl

/-- Reindex the CKR permutation-label extension from label-first block form to
the input-first convention used by `ancillaNormalizedTraceAction`. -/
def inputPermutationLabelEquiv {r : Type w} {n : ℕ} :
    Equiv (Prod (Equiv.Perm (Fin n)) (Prod (TensorPower a n) r))
      (Prod (TensorPower a n) (Prod r (Equiv.Perm (Fin n)))) where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x with | mk xA xrπ => cases xrπ; rfl

private theorem trace_submatrix_equiv_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : CMatrix κ) :
    (M.submatrix e e).trace = M.trace := by
  classical
  unfold Matrix.trace
  exact Fintype.sum_equiv e (fun i => M (e i) (e i)) (fun k => M k k) (by simp)

private theorem classical_blockDiagonal_posSemidef {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, (blocks i).PosSemidef) :
    (Classical.blockDiagonal blocks).PosSemidef := by
  classical
  unfold Classical.blockDiagonal
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (posSemidef_single i).kronecker (hblocks i)

private theorem classical_blockDiagonal_trace {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) :
    (Classical.blockDiagonal blocks).trace = ∑ i, (blocks i).trace := by
  classical
  unfold Classical.blockDiagonal
  simp only [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.trace, Matrix.kronecker, Matrix.single]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    have hji : ¬ i = j := fun hij => hj hij.symm
    simp [hji]

private theorem trace_mul_block_decomp_complex {ι : Type w} {β : Type x}
    [Fintype ι] [Fintype β]
    {H P : CMatrix (Prod ι β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j -> H (i, x) (j, y) = 0) :
    (H * P).trace = ∑ i : ι, ((Classical.block H i i) * Classical.block P i i).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Classical.block, Fintype.sum_prod_type]
  calc
    (∑ i : ι, ∑ x : β, ∑ j : ι, ∑ y : β,
        H (i, x) (j, y) * P (j, y) (i, x)) =
      ∑ i : ι, ∑ x : β, ∑ y : β,
        H (i, x) (i, y) * P (i, y) (i, x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hji => by
          have hij : i ≠ j := fun h => hji h.symm
          simp [hoff i j x, hij])]
    _ = ∑ i : ι, ∑ x : β, ∑ y : β,
        H (i, x) (i, y) * P (i, y) (i, x) := rfl

private theorem trace_mul_block_decomp {ι : Type w} {β : Type x}
    [Fintype ι] [Fintype β]
    {H P : CMatrix (Prod ι β)}
    (hoff : ∀ (i j : ι) (x y : β), i ≠ j -> H (i, x) (j, y) = 0) :
    ((H * P).trace).re =
      ∑ i : ι, ((((Classical.block H i i) * Classical.block P i i).trace).re) := by
  rw [trace_mul_block_decomp_complex (H := H) (P := P) hoff]
  simp

private theorem classical_block_posSemidef {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M.PosSemidef) (i : ι) :
    (Classical.block M i i).PosSemidef := by
  simpa [Classical.block] using hM.submatrix (fun x : β => (i, x))

private theorem classical_block_le_one {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M ≤ 1) (i : ι) :
    Classical.block M i i ≤ 1 := by
  rw [Matrix.le_iff] at hM ⊢
  have h := hM.submatrix (fun x : β => (i, x))
  convert h using 1
  ext x y
  simp [Classical.block, Matrix.sub_apply, Matrix.one_apply]

private theorem classical_block_isHermitian {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {M : CMatrix (Prod ι β)} (hM : M.IsHermitian) (i : ι) :
    (Classical.block M i i).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  simpa [Classical.block, Matrix.conjTranspose] using congrFun (congrFun hM (i, x)) (i, y)

private theorem classical_blockDiagonal_offdiag {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) {i j : ι} (hij : i ≠ j) (x y : β) :
    Classical.blockDiagonal blocks (i, x) (j, y) = 0 := by
  have h := congrFun (congrFun (Classical.blockDiagonal_block_ne blocks hij) x) y
  simpa [Classical.block] using h

private theorem classical_blockDiagonal_block_self_apply {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (i : ι) (x y : β) :
    Classical.blockDiagonal blocks (i, x) (i, y) = blocks i x y := by
  have h := congrFun (congrFun (Classical.blockDiagonal_block_self blocks i) x) y
  simpa [Classical.block] using h

private theorem classical_blockDiagonal_isHermitian {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, (blocks i).IsHermitian) :
    (Classical.blockDiagonal blocks).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  rcases x with ⟨xi, xb⟩
  rcases y with ⟨yi, yb⟩
  change star (Classical.blockDiagonal blocks (yi, yb) (xi, xb)) =
    Classical.blockDiagonal blocks (xi, xb) (yi, yb)
  by_cases hxy : xi = yi
  · subst hxy
    rw [classical_blockDiagonal_block_self_apply, classical_blockDiagonal_block_self_apply]
    simpa [Matrix.IsHermitian, Matrix.conjTranspose] using congrFun (congrFun (hblocks xi) xb) yb
  · have hyx : yi ≠ xi := fun h => hxy h.symm
    rw [classical_blockDiagonal_offdiag blocks hyx, classical_blockDiagonal_offdiag blocks hxy]
    simp

private theorem posPart_trace_blockDiagonal_le_sum {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) :
    (((Classical.blockDiagonal blocks)⁺).trace).re ≤ ∑ i : ι, (((blocks i)⁺).trace).re := by
  classical
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (Prod ι β) := positiveSpectralProjector H hH
  have hscore : ((H * P).trace).re = (H⁺).trace.re := by
    simpa [P] using positiveSpectralProjector_score_eq_posPart_trace H hH
  rw [← hscore]
  rw [trace_mul_block_decomp (H := H) (P := P) (by
    intro i j x y hij
    exact classical_blockDiagonal_offdiag blocks hij x y)]
  refine Finset.sum_le_sum fun i _ => ?_
  have hblockH : Classical.block H i i = blocks i := by
    dsimp [H]
    exact Classical.blockDiagonal_block_self blocks i
  rw [hblockH]
  exact hermitian_trace_mul_effect_le_posPart_trace (blocks i) (Classical.block P i i)
    (hblocks i) (classical_block_posSemidef (positiveSpectralProjector_posSemidef H hH) i)
    (classical_block_le_one (positiveSpectralProjector_le_one H hH) i)

private theorem classical_blockDiagonal_le_one {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β) (hblocks : ∀ i, blocks i ≤ 1) :
    Classical.blockDiagonal blocks ≤ 1 := by
  rw [Matrix.le_iff]
  have hcomp :
      (1 : CMatrix (Prod ι β)) - Classical.blockDiagonal blocks =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) := by
    ext x y
    rcases x with ⟨xi, xb⟩
    rcases y with ⟨yi, yb⟩
    by_cases hxy : xi = yi
    · subst hxy
      change (1 : CMatrix (Prod ι β)) (xi, xb) (xi, yb) -
          Classical.blockDiagonal blocks (xi, xb) (xi, yb) =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) (xi, xb) (xi, yb)
      rw [classical_blockDiagonal_block_self_apply blocks xi xb yb]
      rw [classical_blockDiagonal_block_self_apply
        (fun i => (1 : CMatrix β) - blocks i) xi xb yb]
      simp [Matrix.sub_apply, Matrix.one_apply]
    · have hpair : (xi, xb) ≠ (yi, yb) := by
        intro h
        exact hxy (Prod.ext_iff.mp h).1
      change (1 : CMatrix (Prod ι β)) (xi, xb) (yi, yb) -
          Classical.blockDiagonal blocks (xi, xb) (yi, yb) =
        Classical.blockDiagonal (fun i => (1 : CMatrix β) - blocks i) (xi, xb) (yi, yb)
      rw [classical_blockDiagonal_offdiag blocks hxy xb yb]
      rw [classical_blockDiagonal_offdiag (fun i => (1 : CMatrix β) - blocks i) hxy xb yb]
      simp [hpair]
  rw [hcomp]
  exact classical_blockDiagonal_posSemidef (fun i => (1 : CMatrix β) - blocks i) (fun i => by
    rw [← Matrix.le_iff]
    exact hblocks i)

private theorem sum_posPart_trace_le_blockDiagonal {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) :
    (∑ i : ι, (((blocks i)⁺).trace).re) ≤
      (((Classical.blockDiagonal blocks)⁺).trace).re := by
  classical
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  let P : CMatrix (Prod ι β) :=
    Classical.blockDiagonal (fun i : ι => positiveSpectralProjector (blocks i) (hblocks i))
  have hPpos : P.PosSemidef := by
    dsimp [P]
    exact classical_blockDiagonal_posSemidef _
      (fun i => positiveSpectralProjector_posSemidef (blocks i) (hblocks i))
  have hPle : P ≤ 1 := by
    dsimp [P]
    exact classical_blockDiagonal_le_one _
      (fun i => positiveSpectralProjector_le_one (blocks i) (hblocks i))
  have htrace :
      ((H * P).trace).re =
        ∑ i : ι, ((((blocks i) * positiveSpectralProjector (blocks i) (hblocks i)).trace).re) := by
    simpa [H, P] using trace_mul_block_decomp
      (H := H) (P := P) (by
        intro i j x y hij
        dsimp [H]
        exact classical_blockDiagonal_offdiag blocks hij x y)
  calc
    (∑ i : ι, (((blocks i)⁺).trace).re) =
        ∑ i : ι, ((((blocks i) * positiveSpectralProjector (blocks i) (hblocks i)).trace).re) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (positiveSpectralProjector_score_eq_posPart_trace (blocks i) (hblocks i)).symm
    _ = ((H * P).trace).re := htrace.symm
    _ ≤ ((H⁺).trace).re := by
      exact hermitian_trace_mul_effect_le_posPart_trace H P hH hPpos hPle

private theorem traceNorm_classical_blockDiagonal_eq_sum {ι : Type w} {β : Type x}
    [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (blocks : ι → CMatrix β)
    (hblocks : ∀ i, (blocks i).IsHermitian) (htr : ∀ i, (blocks i).trace = 0) :
    traceNorm (Classical.blockDiagonal blocks) = ∑ i : ι, traceNorm (blocks i) := by
  classical
  let H : CMatrix (Prod ι β) := Classical.blockDiagonal blocks
  have hH : H.IsHermitian := classical_blockDiagonal_isHermitian blocks hblocks
  have hHtr : H.trace = 0 := by
    have htrace : H.trace = ∑ i : ι, (blocks i).trace := by
      dsimp [H]
      exact classical_blockDiagonal_trace blocks
    rw [htrace]
    simp [htr]
  have hnormH := traceNorm_eq_two_posPart_trace_re_of_trace_zero H hH hHtr
  have hnormBlocks :
      (∑ i : ι, traceNorm (blocks i)) =
        ∑ i : ι, 2 * (((blocks i)⁺).trace).re := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact traceNorm_eq_two_posPart_trace_re_of_trace_zero (blocks i) (hblocks i) (htr i)
  rw [hnormH, hnormBlocks, ← Finset.mul_sum]
  congr 1
  exact le_antisymm
    (posPart_trace_blockDiagonal_le_sum blocks hblocks)
    (sum_posPart_trace_le_blockDiagonal blocks hblocks)

private theorem traceNorm_real_smul_eq {β : Type x} [Fintype β] [DecidableEq β]
    {c : ℝ} (hc : 0 ≤ c) (M : CMatrix β) :
    traceNorm (((c : ℂ) • M)) = c * traceNorm M := by
  by_cases hcz : c = 0
  · simp [hcz]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    apply le_antisymm
    · exact traceNorm_real_smul_le hc M
    · have hInvNonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr hc
      have hle := traceNorm_real_smul_le hInvNonneg (((c : ℂ) • M))
      have hscale : (((c⁻¹ : ℝ) : ℂ) • ((c : ℂ) • M)) = M := by
        rw [smul_smul]
        have hcC : ((c : ℂ) ≠ 0) := by exact_mod_cast hcz
        simp [hcC]
      rw [hscale] at hle
      have hmul := mul_le_mul_of_nonneg_left hle hc
      have htrace_nonneg : 0 ≤ traceNorm (((c : ℂ) • M)) :=
        traceNorm_nonneg _
      have hc_inv : c * c⁻¹ = 1 := mul_inv_cancel₀ hcz
      nlinarith

/-- CKR permutation-labelled extension
`1/n! ∑π (π ⊗ id)(ω) ⊗ |π⟩⟨π|`, reindexed so the channel input remains the
left factor.  Its input marginal is the ordinary input permutation twirl. -/
def inputPermutationLabelExtension {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    State (Prod (TensorPower a n) (Prod r (Equiv.Perm (Fin n)))) where
  matrix :=
    (Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      ).submatrix
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
        (inputPermutationLabelEquiv (a := a) (r := r) (n := n)).symm
  pos := by
    classical
    apply Matrix.PosSemidef.submatrix
    apply classical_blockDiagonal_posSemidef
    intro π
    have hcR : 0 ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg _)
    have hcC : 0 ≤ ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)) := by
      exact_mod_cast hcR
    exact ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).pos).smul hcC
  trace_eq_one := by
    classical
    rw [trace_submatrix_equiv_local]
    rw [classical_blockDiagonal_trace]
    simp only [Matrix.trace_smul, State.trace_eq_one, Finset.sum_const, nsmul_eq_mul]
    have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    have hcard_neR : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero :
        Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
    simp only [smul_eq_mul, mul_one] at *
    change (Fintype.card (Equiv.Perm (Fin n)) : ℂ) *
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) = 1
    norm_num [hcard_ne]

private theorem inputPermutationLabelExtension_slice_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r))
    (π : Equiv.Perm (Fin n)) (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
      (i, (j, π)) (i', (j', π)) =
      ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
          (i, j) (i', j')) := by
  dsimp [State.inputPermutationLabelExtension]
  simp only [State.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single, Matrix.smul_apply]
  rw [Finset.sum_eq_single π]
  · simp
  · intro σ _ hσ
    have hne : σ ≠ π := hσ
    simp [hne]
  · intro hnot
    simp at hnot

private theorem inputPermutationLabelExtension_slice_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r))
    {π σ : Equiv.Perm (Fin n)} (hπσ : π ≠ σ)
    (i i' : TensorPower a n) (j j' : r) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
      (i, (j, π)) (i', (j', σ)) = 0 := by
  dsimp [State.inputPermutationLabelExtension]
  simp only [State.inputPermutationLabelEquiv, Classical.blockDiagonal, Matrix.sum_apply,
    Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single, Matrix.smul_apply]
  refine Finset.sum_eq_zero fun τ _ => ?_
  by_cases hτπ : τ = π
  · subst hτπ
    simp [hπσ]
  · simp [hτπ]

/-- The input marginal of the permutation-labelled extension is the ordinary
input permutation twirl. -/
theorem inputPermutationLabelExtension_marginalA_eq_inputPermutationTwirling_marginalA
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).marginalA =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA := by
  apply State.ext
  ext i i'
  simp only [State.marginalA, partialTraceB]
  rw [Fintype.sum_prod_type]
  simp only [inputPermutationLabelExtension_slice_same]
  simp [State.inputPermutationTwirling, Matrix.smul_apply, Matrix.sum_apply,
    Finset.mul_sum]

/-- The input marginal of the permutation-labelled extension is permutation
invariant. -/
theorem inputPermutationLabelExtension_marginalA_isPermutationInvariant
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    (ω.inputPermutationLabelExtension (a := a) (r := r)).marginalA.IsPermutationInvariant
      (a := a) := by
  rw [inputPermutationLabelExtension_marginalA_eq_inputPermutationTwirling_marginalA]
  exact inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω

private def outputPermutationLabelEquiv {r : Type w} {b : Type x} {n : ℕ} :
    Equiv (Prod b (Prod r (Equiv.Perm (Fin n))))
      (Prod (Equiv.Perm (Fin n)) (Prod b r)) where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv := by intro x; cases x with | mk xb xrπ => cases xrπ; rfl
  right_inv := by intro x; cases x with | mk xπ xbr => cases xbr; rfl

private theorem inputPermutationLabelExtension_action_block_same
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) (π : Equiv.Perm (Fin n)) :
    MatrixMap.blockCompression (β := Prod b r) π
      ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
        MatrixMap.kron Δ (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix) := by
  ext br br'
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  simp only [MatrixMap.blockCompression_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change Δ
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', π))) bo bo' =
    ((((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
      Δ (fun i i' =>
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
          (i, rr) (i', rr'))) bo bo'
  have hslice :
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', π))) =
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          (fun i i' =>
            (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
              (i, rr) (i', rr')) := by
    ext i i'
    exact inputPermutationLabelExtension_slice_same
      (a := a) (r := r) (n := n) ω π i i' rr rr'
  rw [hslice]
  let c : ℂ := (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ)
  let X : CMatrix (TensorPower a n) := fun i i' =>
    (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix
      (i, rr) (i', rr')
  have hlin : Δ (c • X) = c • Δ X := LinearMap.map_smul Δ c X
  change Δ (c • X) bo bo' = (c • Δ X) bo bo'
  exact congrFun (congrFun hlin bo) bo'

private theorem inputPermutationLabelExtension_action_block_ne
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) {π σ : Equiv.Perm (Fin n)}
    (hπσ : π ≠ σ) (br br' : Prod b r) :
    ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm)
        (π, br) (σ, br') = 0 := by
  rcases br with ⟨bo, rr⟩
  rcases br' with ⟨bo', rr'⟩
  simp only [Matrix.submatrix_apply]
  rw [MatrixMap.kron_idChannel_apply_slice]
  change Δ
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', σ))) bo bo' = 0
  have hslice :
      (fun i i' =>
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
          (i, (rr, π)) (i', (rr', σ))) = 0 := by
    ext i i'
    exact inputPermutationLabelExtension_slice_ne
      (a := a) (r := r) (n := n) ω hπσ i i' rr rr'
  rw [hslice]
  exact congrFun (congrFun (map_zero Δ) bo) bo'

private theorem inputPermutationLabelExtension_action_reindexed_eq_blockDiagonal
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Δ : MatrixMap (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) :
    ((MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix).submatrix
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) =
      Classical.blockDiagonal (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
  ext x y
  rcases x with ⟨π, br⟩
  rcases y with ⟨σ, br'⟩
  by_cases hπσ : π = σ
  · subst hπσ
    have hblock := congrFun (congrFun
      (inputPermutationLabelExtension_action_block_same
        (a := a) (r := r) (b := b) Δ ω π) br) br'
    have hself := classical_blockDiagonal_block_self_apply
      (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      π br br'
    exact hblock.trans hself.symm
  · rw [inputPermutationLabelExtension_action_block_ne
      (a := a) (r := r) (b := b) Δ ω hπσ br br']
    rw [classical_blockDiagonal_offdiag
      (fun π : Equiv.Perm (Fin n) =>
        (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      hπσ br br']

private theorem cMatrix_isHermitian_real_smul {β : Type x} [Fintype β] [DecidableEq β]
    {c : ℝ} {M : CMatrix β} (hM : M.IsHermitian) :
    (((c : ℂ) • M) : CMatrix β).IsHermitian := by
  exact hM.smul (by simp [IsSelfAdjoint])

private theorem inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    {r : Type w} [Fintype r] [DecidableEq r]
    {b : Type x} [Fintype b] [DecidableEq b]
    {n : ℕ} (Φ Ψ : Channel (TensorPower a n) b)
    (ω : State (Prod (TensorPower a n) r)) :
    traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ)
        (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
        (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix) =
      ∑ π : Equiv.Perm (Fin n),
        traceNorm
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
  classical
  let Δ : MatrixMap (TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let M : CMatrix (Prod b (Prod r (Equiv.Perm (Fin n)))) :=
    MatrixMap.kron Δ (Channel.idChannel (Prod r (Equiv.Perm (Fin n)))).map
      (ω.inputPermutationLabelExtension (a := a) (r := r)).matrix
  let blocks : Equiv.Perm (Fin n) → CMatrix (Prod b r) := fun π =>
    (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
      MatrixMap.kron Δ (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
  have hEq :
      M.submatrix (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
          (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm =
        Classical.blockDiagonal blocks := by
    simpa [M, blocks, Δ] using
      inputPermutationLabelExtension_action_reindexed_eq_blockDiagonal
        (a := a) (r := r) (b := b) Δ ω
  have hblocks : ∀ π, (blocks π).IsHermitian := by
    intro π
    simpa [blocks, Δ] using cMatrix_isHermitian_real_smul
      (c := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹)
      (M := MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
      (MatrixMap.channelDifference_kron_id_apply_isHermitian
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω))
  have htr : ∀ π, (blocks π).trace = 0 := by
    intro π
    dsimp [blocks, Δ]
    rw [Matrix.trace_smul]
    simp [MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
      (a := TensorPower a n) (b := b) (r := r) Φ Ψ
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω)]
  calc
    traceNorm M =
        traceNorm
          (M.submatrix (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm
            (outputPermutationLabelEquiv (b := b) (r := r) (n := n)).symm) := by
          rw [traceNorm_submatrix_equiv]
    _ = traceNorm (Classical.blockDiagonal blocks) := by rw [hEq]
    _ = ∑ π : Equiv.Perm (Fin n), traceNorm (blocks π) :=
          traceNorm_classical_blockDiagonal_eq_sum blocks hblocks htr
    _ = ∑ π : Equiv.Perm (Fin n),
        traceNorm
          (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℂ) •
            MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
          rfl

/-- Canonical purification of a tensor-power state, reindexed as a state on
`(H × H)^n`.  This is the symmetric-lift input used by the CKR post-selection
reduction. -/
def canonicalTensorPowerPurificationState {n : ℕ} (ρ : State (TensorPower a n)) :
    State (TensorPower (Prod a a) n) :=
  ρ.canonicalPurification.state.reindex (tensorPowerProdEquiv a a n).symm

/-- Amplitude of `canonicalTensorPowerPurificationState`. -/
def canonicalTensorPowerPurificationAmp {n : ℕ} (ρ : State (TensorPower a n)) :
    TensorPower (Prod a a) n → ℂ :=
  fun x => ρ.canonicalPurification.amp ((tensorPowerProdEquiv a a n) x)

/-- Canonical purification of a tensor-power state with the purified system in
the first factor after reindexing as `H^n × H^n`.  This orientation matches the
finite diamond-distance convention where the channel acts on the first factor. -/
def inputCanonicalTensorPowerPurificationState {n : ℕ} (ρ : State (TensorPower a n)) :
    State (TensorPower (Prod a a) n) :=
  ρ.canonicalPurification.state.reindex
    ((Equiv.prodComm (TensorPower a n) (TensorPower a n)).trans
      (tensorPowerProdEquiv a a n).symm)

/-- Amplitude of `inputCanonicalTensorPowerPurificationState`. -/
def inputCanonicalTensorPowerPurificationAmp {n : ℕ} (ρ : State (TensorPower a n)) :
    TensorPower (Prod a a) n → ℂ :=
  fun x => ρ.sqrtMatrix ((tensorPowerProdEquiv a a n x).1)
    ((tensorPowerProdEquiv a a n x).2)

@[simp]
theorem canonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.matrix =
      rankOneMatrix ρ.canonicalTensorPowerPurificationAmp := by
  ext x y
  simp [canonicalTensorPowerPurificationState, canonicalTensorPowerPurificationAmp,
    State.reindex_matrix, PureVector.state_matrix, rankOneMatrix_apply]

@[simp]
theorem inputCanonicalTensorPowerPurificationState_matrix {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.matrix =
      rankOneMatrix ρ.inputCanonicalTensorPowerPurificationAmp := by
  ext x y
  simp [inputCanonicalTensorPowerPurificationState, inputCanonicalTensorPowerPurificationAmp,
    State.reindex_matrix, PureVector.state_matrix, rankOneMatrix_apply,
    State.canonicalPurification, State.canonicalPurificationAmp]

/-- Reindexing the tensor-power canonical purification back to
`H^n × H^n` recovers the library's ordinary canonical purification. -/
theorem canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.canonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state := by
  apply State.ext
  ext x y
  simp [canonicalTensorPowerPurificationState, State.reindex]

/-- Reindexing the input-first tensor-power canonical purification back to
`H^n × H^n` gives the ordinary canonical purification with its two factors
swapped. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.inputCanonicalTensorPowerPurificationState.reindex (tensorPowerProdEquiv a a n) =
      ρ.canonicalPurification.state.reindex
        (Equiv.prodComm (TensorPower a n) (TensorPower a n)) := by
  apply State.ext
  ext x y
  simp [inputCanonicalTensorPowerPurificationState, State.reindex]

/-- The right marginal of the tensor-power canonical purification, after
reindexing as `H^n × H^n`, is the purified input state. -/
theorem canonicalTensorPowerPurificationState_reindex_marginalB {n : ℕ}
    (ρ : State (TensorPower a n)) :
    (ρ.canonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).marginalB = ρ := by
  rw [canonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply State.ext
  change partialTraceA (a := TensorPower a n) (b := TensorPower a n)
      ρ.canonicalPurification.state.matrix = ρ.matrix
  exact PureVector.partialTraceA_state_matrix_eq_of_purifies
    ρ.canonicalPurification_purifies

/-- The first marginal of the input-first tensor-power canonical purification,
after reindexing as `H^n × H^n`, is the purified input state. -/
theorem inputCanonicalTensorPowerPurificationState_reindex_marginalA {n : ℕ}
    (ρ : State (TensorPower a n)) :
    (ρ.inputCanonicalTensorPowerPurificationState.reindex
        (tensorPowerProdEquiv a a n)).marginalA = ρ := by
  rw [inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
  apply State.ext
  ext i j
  change partialTraceB (a := TensorPower a n) (b := TensorPower a n)
      ((ρ.canonicalPurification.state.reindex
        (Equiv.prodComm (TensorPower a n) (TensorPower a n))).matrix) i j =
    ρ.matrix i j
  simp [partialTraceB, State.reindex, State.canonicalPurification,
    State.canonicalPurificationAmp, PureVector.state_matrix, rankOneMatrix_apply]
  rw [← ρ.sqrtMatrix_mul_self]
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrArg star (ρ.sqrtMatrix_isHermitian.apply j x)
  simpa using (congrArg (fun z => ρ.sqrtMatrix i x * z) h).symm

end State

private theorem posSemidef_one_sub_of_posSemidef_idempotent (P : CMatrix a)
    (hPpos : P.PosSemidef) (hPid : P * P = P) :
    (1 - P).PosSemidef := by
  let Q : CMatrix a := 1 - P
  have hPherm : P.IsHermitian := hPpos.isHermitian
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact Matrix.IsHermitian.sub (by simp [Matrix.IsHermitian]) hPherm
  have hQid : Q * Q = Q := by
    dsimp [Q]
    calc
      (1 - P) * (1 - P) = (1 - P) * 1 - (1 - P) * P := by
        rw [Matrix.mul_sub]
      _ = (1 - P) - (1 * P - P * P) := by
        rw [Matrix.mul_one, Matrix.sub_mul]
      _ = 1 - P := by
        rw [Matrix.one_mul, hPid]
        abel
  have hPSD : (Matrix.conjTranspose Q * Q).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self Q
  convert hPSD using 1
  rw [hQherm.eq, hQid]

private theorem rankOneMatrix_le_one_of_trace_eq_one (ψ : a → ℂ)
    (hnorm : (rankOneMatrix ψ).trace = 1) :
    rankOneMatrix ψ ≤ (1 : CMatrix a) := by
  rw [Matrix.le_iff]
  have hpos : (rankOneMatrix ψ).PosSemidef := rankOneMatrix_pos ψ
  have hid : rankOneMatrix ψ * rankOneMatrix ψ = rankOneMatrix ψ := by
    let Ψ : PureVector a := ⟨ψ, hnorm⟩
    simpa [Ψ, PureVector.state_matrix] using Ψ.state_matrix_mul_self
  exact posSemidef_one_sub_of_posSemidef_idempotent (rankOneMatrix ψ) hpos hid

private theorem rankOneMatrix_mul_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ) (hψ : P.mulVec ψ = ψ) :
    P * rankOneMatrix ψ = rankOneMatrix ψ := by
  ext i j
  rw [Matrix.mul_apply, rankOneMatrix_apply]
  calc
    ∑ k, P i k * (ψ k * star (ψ j))
        = (∑ k, P i k * ψ k) * star (ψ j) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
    _ = ψ i * star (ψ j) := by
            rw [show ∑ k, P i k * ψ k = ψ i by
              simpa [Matrix.mulVec] using congrFun hψ i]

private theorem rankOneMatrix_mul_right_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ) (hPherm : P.IsHermitian)
    (hψ : P.mulVec ψ = ψ) :
    rankOneMatrix ψ * P = rankOneMatrix ψ := by
  have hrow (j : a) : (∑ k, star (ψ k) * P k j) = star (ψ j) := by
    have hconj : (∑ k, P k j * star (ψ k)) = star (ψ j) := by
      have hconj := congrArg star
        (show ∑ k, P j k * ψ k = ψ j by
          simpa [Matrix.mulVec] using congrFun hψ j)
      simpa [map_sum, map_mul, hPherm.apply] using hconj
    calc
      (∑ k, star (ψ k) * P k j) =
          ∑ k, P k j * star (ψ k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
      _ = star (ψ j) := hconj
  ext i j
  calc
    (rankOneMatrix ψ * P) i j
        = ψ i * (∑ k, star (ψ k) * P k j) := by
            simp [Matrix.mul_apply, rankOneMatrix_apply, Finset.mul_sum, mul_assoc]
    _ = ψ i * star (ψ j) := by rw [hrow]
    _ = rankOneMatrix ψ i j := by simp [rankOneMatrix_apply]

private theorem rankOneMatrix_le_projection_of_mulVec_eq_self
    (P : CMatrix a) (ψ : a → ℂ)
    (hPpos : P.PosSemidef) (hPid : P * P = P)
    (hψ : P.mulVec ψ = ψ) (hnorm : (rankOneMatrix ψ).trace = 1) :
    rankOneMatrix ψ ≤ P := by
  rw [Matrix.le_iff]
  let R : CMatrix a := rankOneMatrix ψ
  have hPherm : P.IsHermitian := hPpos.isHermitian
  have hRleone : R ≤ (1 : CMatrix a) := by
    simpa [R] using rankOneMatrix_le_one_of_trace_eq_one ψ hnorm
  have hOneSubR : (1 - R).PosSemidef := by
    simpa [Matrix.le_iff] using hRleone
  have hPR : P * R = R := by
    simpa [R] using rankOneMatrix_mul_of_mulVec_eq_self P ψ hψ
  have hRP : R * P = R := by
    simpa [R] using rankOneMatrix_mul_right_of_mulVec_eq_self P ψ hPherm hψ
  have hconj : (P.conjTranspose * (1 - R) * P).PosSemidef :=
    hOneSubR.conjTranspose_mul_mul_same P
  have hEq : P.conjTranspose * (1 - R) * P = P - R := by
    rw [hPherm.eq]
    calc
      P * (1 - R) * P = (P * 1 - P * R) * P := by rw [Matrix.mul_sub]
      _ = (P - R) * P := by rw [Matrix.mul_one, hPR]
      _ = P * P - R * P := by rw [Matrix.sub_mul]
      _ = P - R := by rw [hPid, hRP]
  simpa [hEq, R] using hconj

private theorem psdSqrt_permutationChannel_map {n : ℕ}
    (M : CMatrix (TensorPower a n)) (hM : M.PosSemidef)
    (σ : Equiv.Perm (Fin n)) :
    psdSqrt ((permutationChannel (a := a) n σ).map M) =
      (permutationChannel (a := a) n σ).map (psdSqrt M) := by
  let U : Matrix.unitaryGroup (TensorPower a n) ℂ :=
    ⟨permutationMatrix (a := a) n σ⁻¹, by
      rw [Matrix.mem_unitaryGroup_iff]
      simpa [Matrix.star_eq_conjTranspose] using
        permutationMatrix_mul_conjTranspose_self (a := a) n σ⁻¹⟩
  have hpow := cMatrix_rpow_unitary_conj (a := TensorPower a n) hM U
    (s := (1/2 : ℝ)) (by norm_num)
  rw [permutationChannel_map, permutationChannel_map]
  simpa [psdSqrt, CFC.sqrt_eq_rpow, U, Matrix.star_eq_conjTranspose,
    permutationMatrix_conjTranspose, Equiv.Perm.inv_def, Matrix.mul_assoc] using hpow

namespace State

/-- The positive square root of a permutation-invariant tensor-power state is
fixed by the same permutation channel. -/
theorem sqrtMatrix_permutationChannel_map_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n σ).map ρ.sqrtMatrix = ρ.sqrtMatrix := by
  have hmap : (permutationChannel (a := a) n σ).map ρ.matrix = ρ.matrix := by
    simpa [Channel.applyState] using congrArg State.matrix (hρ σ)
  have hsqrt := psdSqrt_permutationChannel_map (a := a) ρ.matrix ρ.pos σ
  rw [hmap] at hsqrt
  simpa [State.sqrtMatrix] using hsqrt.symm

theorem sqrtMatrix_apply_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x y : TensorPower a n) :
    ρ.sqrtMatrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y) =
      ρ.sqrtMatrix x y := by
  have h := congrFun
    (congrFun (sqrtMatrix_permutationChannel_map_of_invariant (a := a) hρ σ) x) y
  simpa [permutationChannel_map_apply] using h

end State

private theorem tensorPowerProdEquiv_fst_apply {b : Type w}
    [Fintype b] [DecidableEq b]
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).1) i =
      (tensorPowerEquiv n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            simp [tensorPowerProdEquiv, tensorPowerEquiv]
            exact ih tail i

private theorem tensorPowerProdEquiv_snd_apply {b : Type w}
    [Fintype b] [DecidableEq b]
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).2) i =
      (tensorPowerEquiv n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
            simp [tensorPowerProdEquiv, tensorPowerEquiv]
            exact ih tail i

private theorem tensorPowerProdEquiv_permEquiv_fst {b : Type w}
    [Fintype b] [DecidableEq b]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : TensorPower (Prod a b) n) :
    (tensorPowerProdEquiv a b n (permEquiv (a := Prod a b) n σ z)).1 =
      permEquiv (a := a) n σ ((tensorPowerProdEquiv a b n z).1) := by
  apply (tensorPowerEquiv n).injective
  ext i
  rw [tensorPowerProdEquiv_fst_apply]
  rw [tensorPowerEquiv_permEquiv]
  rw [tensorPowerEquiv_permEquiv]
  change ((tensorPowerEquiv n) z (σ⁻¹ i)).1 =
    (tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).1) (σ⁻¹ i))
  rw [tensorPowerProdEquiv_fst_apply]

private theorem tensorPowerProdEquiv_permEquiv_snd {b : Type w}
    [Fintype b] [DecidableEq b]
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : TensorPower (Prod a b) n) :
    (tensorPowerProdEquiv a b n (permEquiv (a := Prod a b) n σ z)).2 =
      permEquiv (a := b) n σ ((tensorPowerProdEquiv a b n z).2) := by
  apply (tensorPowerEquiv n).injective
  ext i
  rw [tensorPowerProdEquiv_snd_apply]
  rw [tensorPowerEquiv_permEquiv]
  rw [tensorPowerEquiv_permEquiv]
  change ((tensorPowerEquiv n) z (σ⁻¹ i)).2 =
    (tensorPowerEquiv n ((tensorPowerProdEquiv a b n z).2) (σ⁻¹ i))
  rw [tensorPowerProdEquiv_snd_apply]

namespace State

theorem canonicalTensorPowerPurificationAmp_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x : TensorPower (Prod a a) n) :
    ρ.canonicalTensorPowerPurificationAmp (permEquiv (a := Prod a a) n σ x) =
      ρ.canonicalTensorPowerPurificationAmp x := by
  simp [canonicalTensorPowerPurificationAmp, State.canonicalPurification,
    State.canonicalPurificationAmp, tensorPowerProdEquiv_permEquiv_fst,
    tensorPowerProdEquiv_permEquiv_snd,
    sqrtMatrix_apply_permEquiv_of_invariant (a := a) hρ σ]

theorem inputCanonicalTensorPowerPurificationAmp_permEquiv_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a))
    (σ : Equiv.Perm (Fin n)) (x : TensorPower (Prod a a) n) :
    ρ.inputCanonicalTensorPowerPurificationAmp (permEquiv (a := Prod a a) n σ x) =
      ρ.inputCanonicalTensorPowerPurificationAmp x := by
  simp [inputCanonicalTensorPowerPurificationAmp, tensorPowerProdEquiv_permEquiv_fst,
    tensorPowerProdEquiv_permEquiv_snd,
    sqrtMatrix_apply_permEquiv_of_invariant (a := a) hρ σ]

theorem canonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.canonicalTensorPowerPurificationAmp ∈ symmetricSubspace (a := Prod a a) n := by
  intro σ
  ext x
  exact canonicalTensorPowerPurificationAmp_permEquiv_of_invariant (a := a) hρ σ x

theorem inputCanonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.inputCanonicalTensorPowerPurificationAmp ∈ symmetricSubspace (a := Prod a a) n := by
  intro σ
  ext x
  exact inputCanonicalTensorPowerPurificationAmp_permEquiv_of_invariant
    (a := a) hρ σ x

/-- The canonical purification of a permutation-invariant tensor-power state,
viewed on `(H × H)^n`, is supported on the symmetric subspace. -/
theorem canonicalTensorPowerPurification_supported_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.canonicalTensorPowerPurificationState.SupportedOnSymmetricSubspace
      (a := Prod a a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [canonicalTensorPowerPurificationState_matrix]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact symmetricProjectionMatrix_posSemidef (a := Prod a a) n
  · exact symmetricProjectionMatrix_idempotent (a := Prod a a) n
  · exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := Prod a a) n ρ.canonicalTensorPowerPurificationAmp).mp
      (canonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant (a := a) hρ)
  · rw [← canonicalTensorPowerPurificationState_matrix]
    exact ρ.canonicalTensorPowerPurificationState.trace_eq_one

/-- The input-first canonical purification of a permutation-invariant
tensor-power state, viewed on `(H × H)^n`, is supported on the symmetric
subspace. -/
theorem inputCanonicalTensorPowerPurification_supported_of_invariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.inputCanonicalTensorPowerPurificationState.SupportedOnSymmetricSubspace
      (a := Prod a a) := by
  dsimp [SupportedOnSymmetricSubspace]
  rw [inputCanonicalTensorPowerPurificationState_matrix]
  apply rankOneMatrix_le_projection_of_mulVec_eq_self
  · exact symmetricProjectionMatrix_posSemidef (a := Prod a a) n
  · exact symmetricProjectionMatrix_idempotent (a := Prod a a) n
  · exact (mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self
      (a := Prod a a) n ρ.inputCanonicalTensorPowerPurificationAmp).mp
      (inputCanonicalTensorPowerPurificationAmp_mem_symmetric_of_invariant (a := a) hρ)
  · rw [← inputCanonicalTensorPowerPurificationState_matrix]
    exact ρ.inputCanonicalTensorPowerPurificationState.trace_eq_one

/-- The canonical purification of the input marginal of a twirled
input-reference state is supported on the joint symmetric subspace. -/
theorem inputPermutationTwirling_canonicalPurification_supported
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    @State.SupportedOnSymmetricSubspace (Prod a a) _ _ n
      (@State.canonicalTensorPowerPurificationState a _ _ n
        ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)) := by
  exact @canonicalTensorPowerPurification_supported_of_invariant a _ _ n
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)
    (inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω)

/-- Input-first version of the symmetric canonical lift for the twirled input
marginal.  This orientation matches the channel-input-first convention of
`diamondTraceDistance`. -/
theorem inputPermutationTwirling_inputCanonicalPurification_supported
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    @State.SupportedOnSymmetricSubspace (Prod a a) _ _ n
      (@State.inputCanonicalTensorPowerPurificationState a _ _ n
        ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)) := by
  exact @inputCanonicalTensorPowerPurification_supported_of_invariant a _ _ n
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)
    (inputPermutationTwirling_marginalA_isPermutationInvariant (a := a) (r := r) ω)

/-- The symmetric canonical lift of the twirled input marginal reduces back to
that twirled input marginal after reindexing as `H^n × H^n` and tracing out the
left reference register. -/
theorem inputPermutationTwirling_canonicalPurification_reindex_marginalB
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    ((State.canonicalTensorPowerPurificationState
          ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)).reindex
        (tensorPowerProdEquiv a a n)).marginalB =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA :=
  canonicalTensorPowerPurificationState_reindex_marginalB
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)

/-- The input-first symmetric canonical lift of the twirled input marginal
reduces back to that twirled input marginal after reindexing as `H^n × H^n`
and tracing out the right reference register. -/
theorem inputPermutationTwirling_inputCanonicalPurification_reindex_marginalA
    {r : Type w} [Fintype r] [DecidableEq r]
    {n : ℕ} (ω : State (Prod (TensorPower a n) r)) :
    ((State.inputCanonicalTensorPowerPurificationState
          ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)).reindex
        (tensorPowerProdEquiv a a n)).marginalA =
      (ω.inputPermutationTwirling (a := a) (r := r)).marginalA :=
  inputCanonicalTensorPowerPurificationState_reindex_marginalA
    ((ω.inputPermutationTwirling (a := a) (r := r)).marginalA)

/-- The `i`th eigenvector of a finite state, packaged as a normalized pure
state. -/
def spectralPureVector (ρ : State a) (i : a) : PureVector a where
  amp := fun x => (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) x i
  trace_rankOne_eq_one := by
    rw [rankOneMatrix_trace, dotProduct]
    apply Complex.ext
    · have h := unitary_col_normSq_sum ρ.pos.isHermitian.eigenvectorUnitary i
      simpa [Complex.normSq] using h
    · simp [mul_comm]

/-- Spectral decomposition of a finite state as a convex combination of pure
eigenvector states. -/
theorem matrix_eq_sum_spectralPureVector (ρ : State a) :
    ρ.matrix = ∑ i : a,
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
        (ρ.spectralPureVector i).state.matrix := by
  let U : Matrix.unitaryGroup a ℂ := ρ.pos.isHermitian.eigenvectorUnitary
  let D : CMatrix a :=
    Matrix.diagonal (fun i => ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ))
  have hspec : ρ.matrix = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, Matrix.IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.isHermitian.spectral_theorem
  calc
    ρ.matrix = (U : CMatrix a) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := hspec
    _ = ∑ i : a,
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
        (ρ.spectralPureVector i).state.matrix := by
        ext x y
        simp [U, D, spectralPureVector, PureVector.state_matrix, rankOneMatrix,
          Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
          Matrix.diagonal, mul_assoc, mul_comm]

/-- The eigenvalue weights in the spectral pure-state decomposition sum to
one. -/
theorem sum_eigenvalues_eq_one (ρ : State a) :
    ∑ i : a, ρ.pos.isHermitian.eigenvalues i = 1 := by
  have h := congrArg Complex.re ρ.pos.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.trace_eq_one] at h
  norm_num at h
  exact h.symm

end State

namespace PureVector

/-- A pure input-reference state is obtained from the canonical purification of
its input marginal by a reference-side isometry, after swapping to the local
purification convention.  This is the pure-state CKR lift adapter used before
the symmetric post-selection reduction. -/
theorem exists_referenceIsometry_reindex_prodComm_eq_applyCanonicalOfMarginalA
    {n : ℕ} (Ψ : PureVector (Prod (TensorPower a n) (TensorPower a n))) :
    ∃ V : ReferenceIsometry (TensorPower a n) (TensorPower a n),
      Ψ.reindex (Equiv.prodComm (TensorPower a n) (TensorPower a n)) =
        V.applyPureVector Ψ.state.marginalA.canonicalPurification := by
  exact exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
    Ψ.state.marginalA.canonicalPurification_purifies
    Ψ.reindex_prodComm_purifies_marginalA
    le_rfl

/-- Input-first version of the reference-isometry purification adapter: a pure
input-reference state is obtained from the canonical purification of its input
marginal by an isometry on the right/reference factor. -/
theorem exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA
    {a : Type u} [Fintype a] [DecidableEq a]
    (Ψ : PureVector (Prod a a)) :
    ∃ V : ReferenceIsometry a a,
      Ψ = V.applyPureVectorRight
        (Ψ.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)) := by
  rcases exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      Ψ.state.marginalA.canonicalPurification_purifies
      Ψ.reindex_prodComm_purifies_marginalA le_rfl with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  apply PureVector.ext_amp
  funext x
  have hx := congrArg (fun Φ : PureVector (Prod a a) => Φ.amp (x.2, x.1)) hV
  simpa [ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    PureVector.reindex_amp, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct] using hx

/-- Pure-state action version of the input-first reference-isometry adapter.
For every pure input-reference state, the channel-difference action is obtained
from the canonical purification of its input marginal, followed by a
right-reference isometry. -/
theorem exists_referenceIsometryRight_channelDifference_action_eq
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    ∃ V : ReferenceIsometry a a,
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          Ω.state.matrix =
        V.applyMatrixRight
          (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
            (Ω.state.marginalA.canonicalPurification.reindex
              (Equiv.prodComm a a)).state.matrix) := by
  rcases Ω.exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  have hAction := MatrixMap.channelDifference_kron_id_apply_applyPureVectorRight
    (a := a) (b := b) (r₁ := a) (r₂ := a) Φ Ψc V
    (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a))
  simpa [← hV] using hAction

/-- Pure-state CKR reduction step: the channel-difference action on an
arbitrary pure input-reference state is no larger than the action on the
canonical purification of its input marginal.  The proof uses only the
right-reference isometry adapter and trace-norm invariance under square
reference isometries. -/
theorem channelDifference_action_traceNorm_le_canonicalOfMarginalA
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          Ω.state.matrix) ≤
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          (Ω.state.marginalA.canonicalPurification.reindex
            (Equiv.prodComm a a)).state.matrix) := by
  rcases Ω.exists_referenceIsometryRight_channelDifference_action_eq Φ Ψc with ⟨V, hV⟩
  rw [hV]
  exact traceNorm_applyMatrixRight_le V
    (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
      (Ω.state.marginalA.canonicalPurification.reindex
        (Equiv.prodComm a a)).state.matrix)

/-- Normalized-action form of
`channelDifference_action_traceNorm_le_canonicalOfMarginalA`. -/
theorem channelDifference_normalizedAction_le_canonicalOfMarginalA
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a a)) :
    MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc) Ω.state ≤
      MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc)
        (Ω.state.marginalA.canonicalPurification.reindex
          (Equiv.prodComm a a)).state := by
  unfold MatrixMap.ancillaNormalizedTraceAction MatrixMap.normalizedTraceAction
  exact mul_le_mul_of_nonneg_left
    (Ω.channelDifference_action_traceNorm_le_canonicalOfMarginalA Φ Ψc) (by norm_num)

/-- Arbitrary-reference version of
`exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA`: if the reference
system is large enough, a pure input-reference state is obtained from the
canonical purification of its input marginal by a right-reference isometry. -/
theorem exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA_of_card_le
    {a : Type u} {r : Type w} [Fintype a] [DecidableEq a] [Fintype r] [DecidableEq r]
    (Ω : PureVector (Prod a r)) (hcard : Fintype.card a ≤ Fintype.card r) :
    ∃ V : ReferenceIsometry a r,
      Ω = V.applyPureVectorRight
        (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)) := by
  rcases exists_referenceIsometry_applyPureVector_eq_of_purifies_same_state
      Ω.state.marginalA.canonicalPurification_purifies
      Ω.reindex_prodComm_purifies_marginalA hcard with ⟨V, hV⟩
  refine ⟨V, ?_⟩
  apply PureVector.ext_amp
  funext x
  have hx := congrArg (fun Φ : PureVector (Prod r a) => Φ.amp (x.2, x.1)) hV
  simpa [ReferenceIsometry.applyPureVectorRight_amp, ReferenceIsometry.applyAmpRight,
    PureVector.reindex_amp, ReferenceIsometry.applyPureVector_amp,
    ReferenceIsometry.applyAmp, Matrix.mulVec, dotProduct] using hx

/-- Arbitrary-reference pure-state CKR reduction step.  The channel-difference
action on a pure extension is no larger than the action on the canonical
purification of its input marginal, provided the reference is large enough to
contain the canonical reference. -/
theorem channelDifference_normalizedAction_le_canonicalOfMarginalA_of_card_le
    {a : Type u} {b : Type v} {r : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype r] [DecidableEq r]
    (Φ Ψc : Channel a b) (Ω : PureVector (Prod a r))
    (hcard : Fintype.card a ≤ Fintype.card r) :
    MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc) Ω.state ≤
      MatrixMap.ancillaNormalizedTraceAction
        (MatrixMap.channelDifference Φ Ψc)
        (Ω.state.marginalA.canonicalPurification.reindex
          (Equiv.prodComm a a)).state := by
  classical
  rcases Ω.exists_referenceIsometryRight_eq_applyCanonicalOfMarginalA_of_card_le hcard
    with ⟨V, hV⟩
  let X : CMatrix (Prod b a) :=
    MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state.matrix
  have hAction :
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel r).map
          Ω.state.matrix =
        V.applyMatrixRight X := by
    have h := MatrixMap.channelDifference_kron_id_apply_applyPureVectorRight
      (a := a) (b := b) (r₁ := a) (r₂ := r) Φ Ψc V
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a))
    simpa [X, ← hV] using h
  have hXHerm : X.IsHermitian := by
    simpa [X] using MatrixMap.channelDifference_kron_id_apply_isHermitian
      (a := a) (b := b) (r := a) Φ Ψc
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state
  have hXtr : X.trace = 0 := by
    simpa [X] using MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
      (a := a) (b := b) (r := a) Φ Ψc
      (Ω.state.marginalA.canonicalPurification.reindex (Equiv.prodComm a a)).state
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel r).map
          Ω.state.matrix) ≤
    (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψc) (Channel.idChannel a).map
          (Ω.state.marginalA.canonicalPurification.reindex
            (Equiv.prodComm a a)).state.matrix)
  rw [hAction]
  change (1 / 2 : ℝ) * traceNorm (V.applyMatrixRight X) ≤
    (1 / 2 : ℝ) * traceNorm X
  exact mul_le_mul_of_nonneg_left
    (MatrixMap.traceNorm_applyMatrixRight_le_of_isHermitian_trace_zero V hXHerm hXtr)
    (by norm_num)

end PureVector

/-- CKR purifying register for the purified de-Finetti reference state.

We use the finite profile basis as the purification label set. -/
abbrev ckrPurifyingRegister (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :=
  TensorPowerProfile (Prod a a) n

instance ckrPurifyingRegisterDecidableEq
    (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :
    DecidableEq (ckrPurifyingRegister a n) :=
  Classical.decEq _

private theorem inv_sqrt_profile_count_mul_inv_sqrt_profile_count
    [Nonempty a] (n : ℕ) :
    ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) *
        ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) =
      ((Fintype.card (ckrPurifyingRegister a n) : ℂ)⁻¹) := by
  have hpos : 0 < (Fintype.card (ckrPurifyingRegister a n) : ℝ) := by
    exact_mod_cast TensorPowerProfile.card_pos (a := Prod a a) n
  have hsqrt_sq :
      (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) *
          (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ) =
        (Fintype.card (ckrPurifyingRegister a n) : ℂ) := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hpos)
  rw [← mul_inv_rev, hsqrt_sq]

/-- CKR purified reference vector for `τ_{H^n K^n N}`.

The vector is the normalized coherent superposition of the normalized profile
vectors, with the profile itself used as the purifying register. -/
def ckrPurifiedReferenceVector [Nonempty a] (n : ℕ) :
    PureVector (Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n)) where
  amp xp :=
    ((Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹) *
      tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1
  trace_rankOne_eq_one := by
    classical
    let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
    let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
    have hcstar : star c = c := by
      simp [c]
    have hc2 : c * c = g⁻¹ := by
      simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
    have hg_ne : g ≠ 0 := by
      dsimp [g]
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
    have hunit :
        ∀ p : ckrPurifyingRegister a n,
          ∑ x : TensorPower (Prod a a) n,
            tensorPowerProfileUnitVector (a := Prod a a) p x *
              star (tensorPowerProfileUnitVector (a := Prod a a) p x) = 1 := by
      intro p
      simpa [Matrix.trace, rankOneMatrix_apply] using
        tensorPowerProfileUnitVector_trace_rankOne_eq_one (a := Prod a a) p
    calc
      (rankOneMatrix
          (fun xp : Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n) =>
            c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1)).trace =
          ∑ xp : Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n),
            (c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1) *
              star (c * tensorPowerProfileUnitVector (a := Prod a a) xp.2 xp.1) := by
            simp [Matrix.trace, rankOneMatrix_apply]
      _ = ∑ p : ckrPurifyingRegister a n,
            ∑ x : TensorPower (Prod a a) n,
              (c * c) *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p x)) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            refine Finset.sum_congr rfl fun x _ => ?_
            calc
              c * tensorPowerProfileUnitVector (a := Prod a a) (x, p).2 (x, p).1 *
                  star (c * tensorPowerProfileUnitVector (a := Prod a a) (x, p).2 (x, p).1) =
                c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                  (star (tensorPowerProfileUnitVector (a := Prod a a) p x) * star c) := by
                  rw [star_mul]
              _ = (c * c) *
                    (tensorPowerProfileUnitVector (a := Prod a a) p x *
                      star (tensorPowerProfileUnitVector (a := Prod a a) p x)) := by
                  rw [hcstar]
                  ring
      _ = ∑ p : ckrPurifyingRegister a n, g⁻¹ := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hc2, ← Finset.mul_sum, hunit p, mul_one]
      _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            simpa [g] using mul_inv_cancel₀ hg_ne

/-- CKR purified de-Finetti reference state. -/
def ckrPurifiedReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower (Prod a a) n) (ckrPurifyingRegister a n)) :=
  (ckrPurifiedReferenceVector (a := a) n).state

@[simp]
theorem ckrPurifiedReferenceState_matrix [Nonempty a] (n : ℕ) :
    (ckrPurifiedReferenceState (a := a) n).matrix =
      rankOneMatrix (ckrPurifiedReferenceVector (a := a) n).amp :=
  rfl

/-- The profile isometry whose columns are the normalized profile vectors. -/
def ckrProfileIsometryMatrix (a : Type v) [Fintype a] [DecidableEq a] (n : ℕ) :
    Matrix (TensorPower (Prod a a) n) (ckrPurifyingRegister a n) ℂ :=
  fun x p => tensorPowerProfileUnitVector (a := Prod a a) p x

theorem ckrProfileIsometryMatrix_mul_conjTranspose [Nonempty a] (n : ℕ) :
    ckrProfileIsometryMatrix a n *
        (ckrProfileIsometryMatrix a n).conjTranspose =
      symmetricProjectionMatrix (a := Prod a a) n := by
  classical
  ext x y
  calc
    (ckrProfileIsometryMatrix a n *
        (ckrProfileIsometryMatrix a n).conjTranspose) x y =
        ∑ p : ckrPurifyingRegister a n,
          tensorPowerProfileUnitVector (a := Prod a a) p x *
            star (tensorPowerProfileUnitVector (a := Prod a a) p y) := by
          simp [ckrProfileIsometryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (∑ p : ckrPurifyingRegister a n,
          rankOneMatrix (tensorPowerProfileUnitVector (a := Prod a a) p)) x y := by
          rw [Matrix.sum_apply]
          rfl
    _ = symmetricProjectionMatrix (a := Prod a a) n x y := by
          rw [symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector]

theorem ckrProfileIsometryMatrix_conjTranspose_mul [Nonempty a] (n : ℕ) :
    (ckrProfileIsometryMatrix a n).conjTranspose *
        ckrProfileIsometryMatrix a n =
      1 := by
  classical
  ext p q
  calc
    ((ckrProfileIsometryMatrix a n).conjTranspose *
        ckrProfileIsometryMatrix a n) p q =
        ∑ x : TensorPower (Prod a a) n,
          star (tensorPowerProfileUnitVector (a := Prod a a) p x) *
            tensorPowerProfileUnitVector (a := Prod a a) q x := by
          simp [ckrProfileIsometryMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
    _ = (1 : CMatrix (ckrPurifyingRegister a n)) p q := by
          rw [tensorPowerProfileUnitVector_inner]
          by_cases hpq : p = q
          · subst q
            simp
          · simp [hpq, Matrix.one_apply]

theorem ckrPurifiedReference_marginal_eq_deFinettiReferenceState
    [Nonempty a] (n : ℕ) :
    (ckrPurifiedReferenceState (a := a) n).marginalA =
      deFinettiReferenceState (a := Prod a a) n := by
  classical
  ext x y
  let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
  let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
  have hcstar : star c = c := by
    simp [c]
  have hc2 : c * c = g⁻¹ := by
    simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
  calc
    (ckrPurifiedReferenceState (a := a) n).marginalA.matrix x y =
        ∑ p : ckrPurifyingRegister a n,
          (c * tensorPowerProfileUnitVector (a := Prod a a) p x) *
            star (c * tensorPowerProfileUnitVector (a := Prod a a) p y) := by
          simp [State.marginalA, partialTraceB, ckrPurifiedReferenceState,
            PureVector.state, ckrPurifiedReferenceVector, c]
    _ = g⁻¹ *
        (∑ p : ckrPurifyingRegister a n,
          rankOneMatrix (tensorPowerProfileUnitVector (a := Prod a a) p) x y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [rankOneMatrix_apply]
          calc
            c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                star (c * tensorPowerProfileUnitVector (a := Prod a a) p y) =
              c * tensorPowerProfileUnitVector (a := Prod a a) p x *
                (star (tensorPowerProfileUnitVector (a := Prod a a) p y) * star c) := by
                rw [star_mul]
            _ = (c * c) *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p y)) := by
                rw [hcstar]
                ring
            _ = g⁻¹ *
                (tensorPowerProfileUnitVector (a := Prod a a) p x *
                  star (tensorPowerProfileUnitVector (a := Prod a a) p y)) := by
                rw [hc2]
    _ = ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) *
        symmetricProjectionMatrix (a := Prod a a) n x y := by
          rw [← Matrix.sum_apply,
            ← symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector (a := Prod a a)]
          rfl
    _ = (deFinettiReferenceState (a := Prod a a) n).matrix x y := by
          simp [deFinettiReferenceState_matrix, Matrix.smul_apply, smul_eq_mul]

/-- CKR purified post-selection reference state, reindexed as
`(H^n × H^n) × N`.  Its first marginal is the source-shaped
`postSelectionReferenceState`. -/
def postSelectionPurifiedReferenceStatePair [Nonempty a] (n : ℕ) :
    State (Prod (Prod (TensorPower a n) (TensorPower a n))
      (ckrPurifyingRegister a n)) :=
  (ckrPurifiedReferenceState (a := a) n).reindex
    (Equiv.prodCongr (tensorPowerProdEquiv a a n)
      (Equiv.refl (ckrPurifyingRegister a n)))

theorem postSelectionPurifiedReferenceStatePair_marginalA [Nonempty a] (n : ℕ) :
    (postSelectionPurifiedReferenceStatePair (a := a) n).marginalA =
      postSelectionReferenceState (a := a) n := by
  rw [postSelectionPurifiedReferenceStatePair]
  rw [State.marginalA_reindex_prodCongr]
  rw [ckrPurifiedReference_marginal_eq_deFinettiReferenceState]

/-- CKR purified post-selection reference state, reindexed as
`H^n × (H^n × N)`, so a channel can act on the first/input factor while the
ordinary reference and the profile purifying register are kept as one joint
ancilla. -/
def postSelectionPurifiedReferenceState [Nonempty a] (n : ℕ) :
    State (Prod (TensorPower a n)
      (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))) :=
  (postSelectionPurifiedReferenceStatePair (a := a) n).reindex
    (Equiv.prodAssoc (TensorPower a n) (TensorPower a n) (ckrPurifyingRegister a n))

/-- Drop a terminal unit register from a matrix. -/
def dropRightUnitMatrix {α : Type u} [Fintype α] [DecidableEq α]
    (X : CMatrix (Prod α PUnit)) : CMatrix α :=
  fun i j => X (i, PUnit.unit) (j, PUnit.unit)

/-- Dropping a terminal unit register is a partial trace over that unit
register, hence it does not increase trace norm. -/
theorem traceNorm_dropRightUnitMatrix_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (X : CMatrix (Prod α PUnit)) :
    traceNorm (dropRightUnitMatrix X) ≤ traceNorm X := by
  have hdrop :
      dropRightUnitMatrix X = partialTraceB (a := α) (b := PUnit) X := by
    ext i j
    simp [dropRightUnitMatrix, partialTraceB]
  rw [hdrop]
  exact traceNorm_partialTraceB_le_matrix X

/-- Applying a trace-nonincreasing CP extraction map on a terminal reference
register and then dropping the unit output does not increase trace norm on
Hermitian trace-zero inputs. -/
theorem traceNorm_dropRightUnitMatrix_kron_id_le_of_traceNonincreasingCP
    {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {T : MatrixMap β PUnit} (hT : T.TraceNonincreasingCP)
    {H : CMatrix (Prod α β)} (hH : H.IsHermitian) (htr : H.trace = 0) :
    traceNorm
        (dropRightUnitMatrix
          ((MatrixMap.kron (Channel.idChannel α).map T) H)) ≤
      traceNorm H := by
  calc
    traceNorm
        (dropRightUnitMatrix
          ((MatrixMap.kron (Channel.idChannel α).map T) H)) ≤
        traceNorm ((MatrixMap.kron (Channel.idChannel α).map T) H) :=
          traceNorm_dropRightUnitMatrix_le _
    _ ≤ traceNorm H :=
          MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
            (MatrixMap.traceNonincreasingCP_id_kron (a := α) hT) hH htr

private theorem idChannel_map_eq_self
    {α : Type u} [Fintype α] [DecidableEq α] (X : CMatrix α) :
    (Channel.idChannel α).map X = X := by
  simp [Channel.idChannel, MatrixMap.ofKraus]

private theorem traceEffectToUnit_single_apply
    {α : Type u} [Fintype α] [DecidableEq α]
    {E : CMatrix α} (hE : E.PosSemidef) (p q : α) :
    MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit = E q p := by
  have h := MatrixMap.traceEffectToUnit_apply_of_posSemidef (a := α)
    (E := E) (X := Matrix.single p q (1 : ℂ)) hE
  have happ := congrFun (congrFun h PUnit.unit) PUnit.unit
  calc
    MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
        PUnit.unit PUnit.unit =
        ((Matrix.single p q (1 : ℂ) * E).trace) := happ
    _ = E q p := by
          rw [Matrix.trace]
          change
            (∑ x : α, (Matrix.single p q (1 : ℂ) * E) x x) = E q p
          rw [Finset.sum_eq_single p]
          · simp [Matrix.mul_apply, Matrix.single]
          · intro r _ hr
            have hpr : p ≠ r := by exact hr.symm
            simp [Matrix.mul_apply, Matrix.single, hpr]
          · intro hp
            simp at hp

private theorem kron_id_traceEffectToUnit_raw_sum
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CMatrix β} (hE : E.PosSemidef)
    (X : CMatrix (Prod α β)) (x y : α) :
    (∑ p : β, ∑ q : β, ∑ i : α, ∑ i' : α,
        X (i, p) (i', q) * Matrix.single i i' (1 : ℂ) x y *
          MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit) =
      ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
  classical
  have hT :
      ∀ p q : β,
        MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit = E q p := by
    intro p q
    exact traceEffectToUnit_single_apply (E := E) hE p q
  calc
    (∑ p : β, ∑ q : β, ∑ i : α, ∑ i' : α,
        X (i, p) (i', q) * Matrix.single i i' (1 : ℂ) x y *
          MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
            PUnit.unit PUnit.unit) =
        ∑ p : β, ∑ q : β,
          X (x, p) (y, q) *
            MatrixMap.traceEffectToUnit E (Matrix.single p q (1 : ℂ))
              PUnit.unit PUnit.unit := by
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · rw [Matrix.single_apply_same]
              ring
            · intro y' _ hy'
              rw [Matrix.single_apply_of_col_ne x x hy' (1 : ℂ)]
              ring
            · intro hnot_mem
              simp at hnot_mem
          · intro x' _ hx'
            apply Finset.sum_eq_zero
            intro y' _
            rw [Matrix.single_apply_of_row_ne hx' y' y (1 : ℂ)]
            ring
          · intro hnot_mem
            simp at hnot_mem
    _ = ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hT p q]

private theorem dropRightUnitMatrix_kron_id_traceEffectToUnit_apply
    {α β : Type u} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {E : CMatrix β} (hE : E.PosSemidef)
    (X : CMatrix (Prod α β)) (x y : α) :
    dropRightUnitMatrix
        ((MatrixMap.kron (Channel.idChannel α).map (MatrixMap.traceEffectToUnit E)) X)
        x y =
      ∑ p : β, ∑ q : β, X (x, p) (y, q) * E q p := by
  classical
  simpa only [dropRightUnitMatrix, MatrixMap.kron, idChannel_map_eq_self] using
    kron_id_traceEffectToUnit_raw_sum (E := E) hE X x y

private theorem matrixMap_trace_weight_commute
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (Δ : MatrixMap α β) (A : γ → γ → CMatrix α) (E : CMatrix γ)
    (x y : β) :
    ((Matrix.of fun j j' => Δ (A j j') x y) * E).trace =
      Δ (fun i i' => ((Matrix.of fun j j' => A j j' i i') * E).trace) x y := by
  simp [Matrix.trace, Matrix.mul_apply]
  have hmap :
      Δ (fun i i' => ∑ j : γ, ∑ j' : γ, A j j' i i' * E j' j) =
        ∑ j : γ, ∑ j' : γ, E j' j • Δ (A j j') := by
    have hfun : (fun i i' => ∑ j : γ, ∑ j' : γ, A j j' i i' * E j' j) =
        ∑ j : γ, ∑ j' : γ, E j' j • A j j' := by
      ext i i'
      simp [Matrix.sum_apply, Matrix.smul_apply, mul_comm]
    rw [hfun]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_smul]
  have happ := congrFun (congrFun hmap x) y
  rw [happ]
  simp [Matrix.sum_apply, Matrix.smul_apply, mul_comm]

private def assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (Prod α (Prod β γ))) : CMatrix (Prod (Prod α β) γ) :=
  X.submatrix (Equiv.prodAssoc α β γ) (Equiv.prodAssoc α β γ)

private theorem traceNorm_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (Prod α (Prod β γ))) :
    traceNorm (assocRightMatrix X) = traceNorm X := by
  simpa [assocRightMatrix] using
    (traceNorm_submatrix_equiv (Equiv.prodAssoc α β γ) X)

private theorem assocRightMatrix_isHermitian
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    {X : CMatrix (Prod α (Prod β γ))} (hX : X.IsHermitian) :
    (assocRightMatrix X).IsHermitian := by
  simpa [assocRightMatrix] using hX.submatrix (Equiv.prodAssoc α β γ)

private theorem trace_assocRightMatrix
    {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (X : CMatrix (Prod α (Prod β γ))) :
    (assocRightMatrix X).trace = X.trace := by
  rw [assocRightMatrix]
  rw [Matrix.trace]
  rw [Matrix.trace]
  exact Fintype.sum_equiv (Equiv.prodAssoc α β γ)
    (fun x : Prod (Prod α β) γ =>
      X (Equiv.prodAssoc α β γ x) (Equiv.prodAssoc α β γ x))
    (fun y : Prod α (Prod β γ) => X y y)
    (by intro x; rfl)

private theorem dropRightUnitMatrix_action_traceEffectToUnit_commute
    {b : Type w} [Fintype b] [DecidableEq b]
    [Nonempty a] {n : ℕ}
    (Δ : MatrixMap (TensorPower a n) b)
    {E : CMatrix (ckrPurifyingRegister a n)} (hE : E.PosSemidef) :
    dropRightUnitMatrix
      ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map
          (MatrixMap.traceEffectToUnit E))
        (assocRightMatrix
          ((MatrixMap.kron Δ
              (Channel.idChannel (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))).map)
            (postSelectionPurifiedReferenceState (a := a) n).matrix))) =
    MatrixMap.kron Δ (Channel.idChannel (TensorPower a n)).map
      ((dropRightUnitMatrix
          ((MatrixMap.kron
              (Channel.idChannel (TensorPower (Prod a a) n)).map
              (MatrixMap.traceEffectToUnit E))
            (ckrPurifiedReferenceState (a := a) n).matrix)).submatrix
        (tensorPowerProdEquiv a a n).symm (tensorPowerProdEquiv a a n).symm) := by
  ext br br'
  simp [assocRightMatrix, dropRightUnitMatrix, postSelectionPurifiedReferenceState,
    postSelectionPurifiedReferenceStatePair, State.reindex,
    MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_left_apply_slice,
    MatrixMap.traceEffectToUnit_apply_of_posSemidef hE]
  exact matrixMap_trace_weight_commute Δ
    (fun j j' => fun i i' =>
      (ckrPurifiedReferenceVector (a := a) n).amp
        ((tensorPowerProdEquiv a a n).symm (i, br.2), j) *
      star ((ckrPurifiedReferenceVector (a := a) n).amp
        ((tensorPowerProdEquiv a a n).symm (i', br'.2), j')))
    E br.1 br'.1

namespace State

variable {n : ℕ}

/-- Profile-coordinate compression of a state by the normalized symmetric
profile isometry. -/
def ckrProfileCoordinateMatrix
    (ρ : State (TensorPower (Prod a a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ckrProfileIsometryMatrix a n).conjTranspose * ρ.matrix *
    ckrProfileIsometryMatrix a n

/-- CKR extraction effect.  The transpose matches the convention of
`MatrixMap.traceEffectToUnit`, whose scalar action on a matrix unit is
`X ↦ Tr(XE)`. -/
def ckrProfileCoordinateEffect
    (ρ : State (TensorPower (Prod a a) n)) :
    CMatrix (ckrPurifyingRegister a n) :=
  (ρ.ckrProfileCoordinateMatrix (a := a)).transpose

theorem ckrProfileCoordinateMatrix_posSemidef
    (ρ : State (TensorPower (Prod a a) n)) :
    (ρ.ckrProfileCoordinateMatrix (a := a)).PosSemidef := by
  exact ρ.pos.conjTranspose_mul_mul_same (ckrProfileIsometryMatrix a n)

theorem ckrProfileCoordinateEffect_posSemidef
    (ρ : State (TensorPower (Prod a a) n)) :
    (ρ.ckrProfileCoordinateEffect (a := a)).PosSemidef := by
  exact (ρ.ckrProfileCoordinateMatrix_posSemidef (a := a)).transpose

theorem ckrProfileCoordinateMatrix_le_one [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.ckrProfileCoordinateMatrix (a := a) ≤ 1 := by
  dsimp [SupportedOnSymmetricSubspace] at hρ
  rw [Matrix.le_iff] at hρ ⊢
  let U := ckrProfileIsometryMatrix a n
  have hconj : (U.conjTranspose *
      (symmetricProjectionMatrix (a := Prod a a) n - ρ.matrix) * U).PosSemidef :=
    hρ.conjTranspose_mul_mul_same U
  convert hconj using 1
  calc
    1 - ρ.ckrProfileCoordinateMatrix (a := a) =
        (U.conjTranspose * symmetricProjectionMatrix (a := Prod a a) n * U) -
          (U.conjTranspose * ρ.matrix * U) := by
          dsimp [ckrProfileCoordinateMatrix, U]
          rw [← ckrProfileIsometryMatrix_mul_conjTranspose (a := a) n]
          rw [← Matrix.mul_assoc, ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n,
            Matrix.one_mul, Matrix.mul_assoc,
            ckrProfileIsometryMatrix_conjTranspose_mul (a := a) n]
    _ = U.conjTranspose *
        (symmetricProjectionMatrix (a := Prod a a) n - ρ.matrix) * U := by
          rw [Matrix.mul_sub, Matrix.sub_mul]

theorem ckrProfileCoordinateEffect_le_one [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.ckrProfileCoordinateEffect (a := a) ≤ 1 := by
  have hC := ρ.ckrProfileCoordinateMatrix_le_one (a := a) hρ
  rw [Matrix.le_iff] at hC
  rw [Matrix.le_iff]
  dsimp [ckrProfileCoordinateEffect]
  convert hC.transpose using 1
  rw [Matrix.transpose_sub, Matrix.transpose_one]

theorem ckrProfileCoordinateEffect_traceNonincreasingCP [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    MatrixMap.TraceNonincreasingCP
      (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))) :=
  MatrixMap.traceEffectToUnit_traceNonincreasingCP
    (ρ.ckrProfileCoordinateEffect_posSemidef (a := a))
    (ρ.ckrProfileCoordinateEffect_le_one (a := a) hρ)

private theorem cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
    {A : CMatrix (TensorPower (Prod a a) n)}
    (hA : A.PosSemidef) (hneg : (-A).PosSemidef) :
    A = 0 := by
  have h0A : (0 : CMatrix (TensorPower (Prod a a) n)) ≤ A := by
    rw [Matrix.le_iff]
    simpa using hA
  have hA0 : A ≤ (0 : CMatrix (TensorPower (Prod a a) n)) := by
    rw [Matrix.le_iff]
    simpa using hneg
  exact le_antisymm hA0 h0A

private theorem symmetricProjection_supported_fixed [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
        symmetricProjectionMatrix (a := Prod a a) n = ρ.matrix := by
  classical
  let P : CMatrix (TensorPower (Prod a a) n) :=
    symmetricProjectionMatrix (a := Prod a a) n
  let Q : CMatrix (TensorPower (Prod a a) n) := 1 - P
  have hPidem : P * P = P := by
    simpa [P] using symmetricProjectionMatrix_idempotent (a := Prod a a) n
  have hPherm : P.IsHermitian := by
    simpa [P] using symmetricProjectionMatrix_isHermitian (a := Prod a a) n
  have hQherm : Q.IsHermitian := by
    dsimp [Q]
    exact symmetricProjectionMatrix_complement_isHermitian (a := Prod a a) n
  have hQP : Q * P = 0 := by
    calc
      Q * P = (1 - P) * P := rfl
      _ = P - P * P := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 0 := by rw [hPidem, sub_self]
  have hPQ : P * Q = 0 := by
    calc
      P * Q = P * (1 - P) := rfl
      _ = P - P * P := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = 0 := by rw [hPidem, sub_self]
  have hdiff : (P - ρ.matrix).PosSemidef := by
    dsimp [SupportedOnSymmetricSubspace, P] at hρ
    rwa [Matrix.le_iff] at hρ
  have hQrhoQ_pos : (Q * ρ.matrix * Q).PosSemidef := by
    have h := ρ.pos.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_pos : (Q * (P - ρ.matrix) * Q).PosSemidef := by
    have h := hdiff.conjTranspose_mul_mul_same Q
    simpa [hQherm.eq] using h
  have hQdiffQ_eq_neg :
      Q * (P - ρ.matrix) * Q = -(Q * ρ.matrix * Q) := by
    have hleft : Q * (P - ρ.matrix) = Q * P - Q * ρ.matrix := by
      rw [Matrix.mul_sub]
    calc
      Q * (P - ρ.matrix) * Q =
          (Q * P - Q * ρ.matrix) * Q := by rw [hleft]
      _ = Q * P * Q - Q * ρ.matrix * Q := by rw [Matrix.sub_mul]
      _ = 0 - Q * ρ.matrix * Q := by rw [hQP, Matrix.zero_mul]
      _ = -(Q * ρ.matrix * Q) := by rw [zero_sub]
  have hQrhoQ_zero : Q * ρ.matrix * Q = 0 :=
    cMatrix_eq_zero_of_posSemidef_and_neg_posSemidef
      hQrhoQ_pos (by simpa [hQdiffQ_eq_neg] using hQdiffQ_pos)
  let S : CMatrix (TensorPower (Prod a a) n) := psdSqrt ρ.matrix
  have hSsq : S * S = ρ.matrix := by
    simpa [S] using psdSqrt_mul_self_of_posSemidef ρ.pos
  have hSherm : S.IsHermitian := by
    simpa [S] using psdSqrt_isHermitian ρ.matrix
  have hSQ_conj_self :
      (S * Q).conjTranspose * (S * Q) = 0 := by
    calc
      (S * Q).conjTranspose * (S * Q) =
          Q * S * (S * Q) := by
          rw [Matrix.conjTranspose_mul, hQherm.eq, hSherm.eq]
      _ = Q * ρ.matrix * Q := by
          calc
            Q * S * (S * Q) = (Q * S * S) * Q := by
              rw [← Matrix.mul_assoc]
            _ = Q * (S * S) * Q := by
              rw [Matrix.mul_assoc Q S S]
            _ = Q * ρ.matrix * Q := by rw [hSsq]
      _ = 0 := hQrhoQ_zero
  have hSQ : S * Q = 0 := by
    have htrace : ((S * Q).conjTranspose * (S * Q)).trace = 0 := by
      rw [hSQ_conj_self, Matrix.trace_zero]
    exact (Matrix.trace_conjTranspose_mul_self_eq_zero_iff).mp htrace
  have hρQ : ρ.matrix * Q = 0 := by
    rw [← hSsq, Matrix.mul_assoc, hSQ, Matrix.mul_zero]
  have hQρ : Q * ρ.matrix = 0 := by
    rw [← Matrix.conjTranspose_eq_zero]
    calc
      (Q * ρ.matrix).conjTranspose =
          ρ.matrix.conjTranspose * Q.conjTranspose := by rw [Matrix.conjTranspose_mul]
      _ = ρ.matrix * Q := by rw [ρ.pos.isHermitian.eq, hQherm.eq]
      _ = 0 := hρQ
  have hPρ : P * ρ.matrix = ρ.matrix := by
    calc
      P * ρ.matrix = (1 - Q) * ρ.matrix := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - Q * ρ.matrix := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = ρ.matrix := by rw [hQρ, sub_zero]
  have hρP : ρ.matrix * P = ρ.matrix := by
    calc
      ρ.matrix * P = ρ.matrix * (1 - Q) := by simp [Q, sub_sub_cancel]
      _ = ρ.matrix - ρ.matrix * Q := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = ρ.matrix := by rw [hρQ, sub_zero]
  calc
    symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
        symmetricProjectionMatrix (a := Prod a a) n =
        P * ρ.matrix * P := rfl
    _ = ρ.matrix * P := by rw [hPρ]
    _ = ρ.matrix := hρP

private theorem ckrProfileCoordinate_reconstruct_of_projection_fixed [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n))
    (hfixed :
      symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
          symmetricProjectionMatrix (a := Prod a a) n = ρ.matrix) :
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
      ρ.matrix := by
  calc
    ckrProfileIsometryMatrix a n *
        ρ.ckrProfileCoordinateMatrix (a := a) *
        (ckrProfileIsometryMatrix a n).conjTranspose =
        ckrProfileIsometryMatrix a n *
          ((ckrProfileIsometryMatrix a n).conjTranspose * ρ.matrix *
            ckrProfileIsometryMatrix a n) *
          (ckrProfileIsometryMatrix a n).conjTranspose := by
          rfl
    _ =
        (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) *
          ρ.matrix *
          (ckrProfileIsometryMatrix a n *
            (ckrProfileIsometryMatrix a n).conjTranspose) := by
          simp [Matrix.mul_assoc]
    _ =
        symmetricProjectionMatrix (a := Prod a a) n * ρ.matrix *
          symmetricProjectionMatrix (a := Prod a a) n := by
          rw [ckrProfileIsometryMatrix_mul_conjTranspose]
    _ = ρ.matrix := hfixed

private theorem dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction [Nonempty a]
    (ρ : State (TensorPower (Prod a a) n)) :
    dropRightUnitMatrix
        ((MatrixMap.kron
            (Channel.idChannel (TensorPower (Prod a a) n)).map
            (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a)))
          (ckrPurifiedReferenceState (a := a) n).matrix)) =
      (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) •
        (ckrProfileIsometryMatrix a n *
          ρ.ckrProfileCoordinateMatrix (a := a) *
          (ckrProfileIsometryMatrix a n).conjTranspose)) := by
  classical
  let U := ckrProfileIsometryMatrix a n
  let C := ρ.ckrProfileCoordinateMatrix (a := a)
  let E := ρ.ckrProfileCoordinateEffect (a := a)
  let g : ℂ := (Fintype.card (ckrPurifyingRegister a n) : ℂ)
  let c : ℂ := (Real.sqrt ((Fintype.card (ckrPurifyingRegister a n) : ℝ)) : ℂ)⁻¹
  have hcstar : star c = c := by
    simp [c]
  have hc2 : c * c = g⁻¹ := by
    simpa [c, g] using inv_sqrt_profile_count_mul_inv_sqrt_profile_count (a := a) n
  have hEpos : E.PosSemidef := by
    simpa [E] using ρ.ckrProfileCoordinateEffect_posSemidef (a := a)
  ext x y
  calc
    dropRightUnitMatrix
        ((MatrixMap.kron
            (Channel.idChannel (TensorPower (Prod a a) n)).map
            (MatrixMap.traceEffectToUnit E)
          (ckrPurifiedReferenceState (a := a) n).matrix)) x y =
        ∑ p : ckrPurifyingRegister a n,
          ∑ q : ckrPurifyingRegister a n,
            (c * U x p * star (c * U y q)) * E q p := by
          rw [dropRightUnitMatrix_kron_id_traceEffectToUnit_apply hEpos]
          refine Finset.sum_congr rfl fun p _ => ?_
          refine Finset.sum_congr rfl fun q _ => ?_
          rfl
    _ =
        g⁻¹ * (∑ p : ckrPurifyingRegister a n,
          ∑ q : ckrPurifyingRegister a n,
            U x p * C p q * star (U y q)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          calc
            c * U x p * star (c * U y q) * C p q =
                c * U x p * (star (U y q) * star c) * C p q := by
                rw [star_mul]
            _ = (c * c) * (U x p * C p q * star (U y q)) := by
                rw [hcstar]
                ring
            _ = g⁻¹ * (U x p * C p q * star (U y q)) := by
                rw [hc2]
    _ =
        (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) •
          (U * C * U.conjTranspose)) x y := by
          have hgcast :
              (((Fintype.card (ckrPurifyingRegister a n) : ℝ)⁻¹ : ℂ) = g⁻¹) := by
            simp [g]
          rw [Matrix.smul_apply, hgcast]
          congr 1
          rw [Finset.sum_comm]
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply,
            Finset.sum_mul, mul_assoc]

/-- CKR `extractpart` with the exact profile-count factor.

Every state supported on the symmetric subspace of `(H ⊗ H)^n` is recovered
from the CKR purified reference state by applying a trace-nonincreasing CP
effect map on the profile purifying register.  The scalar factor is the exact
number of tensor-power profiles, i.e. the rank of the symmetric projection in
the profile basis. -/
theorem ckr_extractpart_profile_count [Nonempty a]
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.matrix =
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix) := by
  classical
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit :=
    MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))
  refine ⟨T, ?_, ?_⟩
  · simpa [T] using ρ.ckrProfileCoordinateEffect_traceNonincreasingCP
      (a := a) hρ
  · have hdrop :=
      dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction (a := a) ρ
    have hfixed := symmetricProjection_supported_fixed (a := a) ρ hρ
    have hrec :=
      ckrProfileCoordinate_reconstruct_of_projection_fixed (a := a) ρ hfixed
    have hdropρ :
        dropRightUnitMatrix
            ((MatrixMap.kron
                (Channel.idChannel (TensorPower (Prod a a) n)).map T)
              (ckrPurifiedReferenceState (a := a) n).matrix) =
          (((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) •
            ρ.matrix) := by
      simpa [T, ckrPurifyingRegister, hrec] using hdrop
    rw [hdropρ]
    symm
    have hcard_ne :
        (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) ≠ 0 := by
      exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
    calc
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) •
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹ •
            ρ.matrix) =
          ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) *
              (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹) •
            ρ.matrix := by
            rw [smul_smul]
      _ = ρ.matrix := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

/-- CKR `extractpart` with the binomial symmetric-dimension factor. -/
theorem ckr_extractpart_choose [Nonempty a]
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ∃ T : MatrixMap (ckrPurifyingRegister a n) PUnit,
      T.TraceNonincreasingCP ∧
        ρ.matrix =
          ((Nat.choose (n + Fintype.card (Prod a a) - 1) n : ℝ) : ℂ) •
            dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix) := by
  classical
  obtain ⟨T, hT, hEq⟩ :=
    ρ.ckr_extractpart_profile_count (a := a) hρ
  refine ⟨T, hT, ?_⟩
  simpa [tensorPowerProfile_card_eq_choose (a := Prod a a) n] using hEq

/-- Concrete `traceEffectToUnit` form of CKR `extractpart`.

This is the witness used in `ckr_extractpart_profile_count`, exposed so the
post-selection assembly can commute a channel-difference action past the
explicit extraction map. -/
theorem ckr_extractpart_profile_count_traceEffect [Nonempty a]
    {n : ℕ} (ρ : State (TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    ρ.matrix =
      ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) : ℂ) •
        dropRightUnitMatrix
          ((MatrixMap.kron
              (Channel.idChannel (TensorPower (Prod a a) n)).map
              (MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))))
            (ckrPurifiedReferenceState (a := a) n).matrix) := by
  classical
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit :=
    MatrixMap.traceEffectToUnit (ρ.ckrProfileCoordinateEffect (a := a))
  have hdrop :=
    dropRightUnitMatrix_ckrExtraction_eq_profile_reconstruction (a := a) ρ
  have hfixed := symmetricProjection_supported_fixed (a := a) ρ hρ
  have hrec :=
    ckrProfileCoordinate_reconstruct_of_projection_fixed (a := a) ρ hfixed
  have hdropρ :
      dropRightUnitMatrix
          ((MatrixMap.kron
              (Channel.idChannel (TensorPower (Prod a a) n)).map T)
            (ckrPurifiedReferenceState (a := a) n).matrix) =
        (((Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ)⁻¹ : ℂ) •
          ρ.matrix) := by
    simpa [T, ckrPurifyingRegister, hrec] using hdrop
  rw [hdropρ]
  symm
  have hcard_ne :
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) ≠ 0 := by
    exact_mod_cast TensorPowerProfile.card_ne_zero (a := Prod a a) n
  calc
    (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) •
        ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹ •
          ρ.matrix) =
        ((Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ) *
            (Fintype.card (TensorPowerProfile (Prod a a) n) : ℂ)⁻¹) •
          ρ.matrix := by
          rw [smul_smul]
    _ = ρ.matrix := by rw [mul_inv_cancel₀ hcard_ne, one_smul]

end State

namespace MatrixMap

theorem ancillaNormalizedTraceAction_le_spectralPure_sum
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : State (Prod a a)) :
    Δ.ancillaNormalizedTraceAction ω ≤
      ∑ i : Prod a a,
        ω.pos.isHermitian.eigenvalues i *
          Δ.ancillaNormalizedTraceAction (ω.spectralPureVector i).state := by
  dsimp [ancillaNormalizedTraceAction, normalizedTraceAction]
  have hmatrix := ω.matrix_eq_sum_spectralPureVector
  have hmap : MatrixMap.kron Δ (Channel.idChannel a).map ω.matrix =
      ∑ i : Prod a a,
        ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel a).map
            (ω.spectralPureVector i).state.matrix := by
    conv_lhs => rw [hmatrix]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hmap]
  have hsum := traceNorm_sum_le_sum_traceNorm
    (Finset.univ : Finset (Prod a a))
    (fun i => ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
      MatrixMap.kron Δ (Channel.idChannel a).map (ω.spectralPureVector i).state.matrix)
  have hterms :
      (∑ i : Prod a a,
        traceNorm (((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          MatrixMap.kron Δ (Channel.idChannel a).map
            (ω.spectralPureVector i).state.matrix)) ≤
        ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact traceNorm_real_smul_le (ω.pos.eigenvalues_nonneg i) _
  calc
    (1 / 2 : ℝ) * traceNorm
        (∑ i : Prod a a,
          ((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
            MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix)
        ≤ (1 / 2 : ℝ) *
          (∑ i : Prod a a,
            traceNorm (((ω.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
              MatrixMap.kron Δ (Channel.idChannel a).map
                (ω.spectralPureVector i).state.matrix)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (∑ i : Prod a a,
            ω.pos.isHermitian.eigenvalues i *
              traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
                (ω.spectralPureVector i).state.matrix)) :=
          mul_le_mul_of_nonneg_left hterms (by norm_num)
    _ = ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            ((1 / 2 : ℝ) * traceNorm (MatrixMap.kron Δ (Channel.idChannel a).map
              (ω.spectralPureVector i).state.matrix)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/-- Convexity bridge for the source-shaped diamond distance: it suffices to
bound the finite-reference action on pure input-reference states. -/
theorem ancillaNormalizedTraceAction_le_of_forall_pure_bound
    {a : Type v} {b : Type w} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (Δ : MatrixMap a b) (ω : State (Prod a a)) {B : ℝ}
    (h : ∀ Ω : PureVector (Prod a a), Δ.ancillaNormalizedTraceAction Ω.state ≤ B) :
    Δ.ancillaNormalizedTraceAction ω ≤ B := by
  calc
    Δ.ancillaNormalizedTraceAction ω ≤
        ∑ i : Prod a a,
          ω.pos.isHermitian.eigenvalues i *
            Δ.ancillaNormalizedTraceAction (ω.spectralPureVector i).state :=
          Δ.ancillaNormalizedTraceAction_le_spectralPure_sum ω
    _ ≤ ∑ i : Prod a a, ω.pos.isHermitian.eigenvalues i * B := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (h (ω.spectralPureVector i))
            (ω.pos.eigenvalues_nonneg i)
    _ = B := by
          rw [← Finset.sum_mul]
          rw [ω.sum_eigenvalues_eq_one]
          simp

variable {n : ℕ}
variable {b : Type w} [Fintype b] [DecidableEq b]

/-- CKR post-selection covariance for a matrix-map difference.

For every tensor-factor permutation `π`, the source assumes a CPTP map `Kπ`
such that `Δ ∘ π = Kπ ∘ Δ`.  The predicate is stated at matrix level using the
project's finite permutation channel. -/
def PostSelectionCovariant (Δ : MatrixMap (QIT.TensorPower a n) b) : Prop :=
  ∀ π : Equiv.Perm (Fin n), ∃ Kπ : Channel b b,
    ∀ X : CMatrix (QIT.TensorPower a n),
      Δ ((permutationChannel (a := a) n π).map X) = Kπ.map (Δ X)

/-- Tensoring a post-selection covariant map with an identity reference keeps
the covariance equation at the finite-ancilla level. -/
theorem postSelectionCovariant_kron_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Δ : MatrixMap (QIT.TensorPower a n) b)
    (hcov : Δ.PostSelectionCovariant (a := a) (n := n))
    (π : Equiv.Perm (Fin n)) (X : CMatrix (Prod (QIT.TensorPower a n) r)) :
    ∃ Kπ : Channel b b,
      MatrixMap.kron Δ (Channel.idChannel r).map
          (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).map X) =
        (Kπ.prod (Channel.idChannel r)).map
          (MatrixMap.kron Δ (Channel.idChannel r).map X) := by
  obtain ⟨Kπ, hKπ⟩ := hcov π
  refine ⟨Kπ, ?_⟩
  change MatrixMap.kron Δ (Channel.idChannel r).map
      (MatrixMap.kron (permutationChannel (a := a) n π).map
        (Channel.idChannel r).map X) =
    MatrixMap.kron Kπ.map (Channel.idChannel r).map
      (MatrixMap.kron Δ (Channel.idChannel r).map X)
  ext br br'
  rw [MatrixMap.kron_idChannel_apply_slice]
  rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice_perm :
      (fun i i' =>
          MatrixMap.kron (permutationChannel (a := a) n π).map
            (Channel.idChannel r).map X (i, br.2) (i', br'.2)) =
        (permutationChannel (a := a) n π).map
          (fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    rw [MatrixMap.kron_idChannel_apply_slice]
  have hslice_delta :
      (fun i i' =>
          MatrixMap.kron Δ (Channel.idChannel r).map X (i, br.2) (i', br'.2)) =
        Δ (fun i i' => X (i, br.2) (i', br'.2)) := by
    ext i i'
    rw [MatrixMap.kron_idChannel_apply_slice]
  rw [hslice_perm, hKπ, hslice_delta]

end MatrixMap

namespace Channel

variable {n : ℕ}
variable {b : Type w} [Fintype b] [DecidableEq b]

/-- CKR post-selection covariance for the difference of two channels. -/
def PostSelectionCovariantDifference (Φ Ψ : Channel (QIT.TensorPower a n) b) : Prop :=
  MatrixMap.PostSelectionCovariant (a := a) (n := n) (b := b)
    (MatrixMap.channelDifference (a := QIT.TensorPower a n) (b := b) Φ Ψ)

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state cannot increase the channel-difference normalized
trace action. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  obtain ⟨Kπ, hEq⟩ :=
    MatrixMap.postSelectionCovariant_kron_permutation_eq (a := a) (b := b) (r := r)
      (MatrixMap.channelDifference Φ Ψ) hcov π ω.matrix
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [Channel.applyState, hEq]
  have hH := MatrixMap.channelDifference_kron_id_apply_isHermitian
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have htr := MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
    (a := QIT.TensorPower a n) (b := b) (r := r) Φ Ψ ω
  have hle := MatrixMap.traceNorm_apply_le_of_traceNonincreasingCP
    (Channel.traceNonincreasingCP_kron_id (r := r) Kπ) hH htr
  exact mul_le_mul_of_nonneg_left (by simpa [Channel.prod] using hle) (by norm_num)

/-- Applying a tensor-factor permutation and then its inverse on the input
register leaves an input-reference state unchanged. -/
private theorem inputPermutation_inv_apply_permutation
    {r : Type x} [Fintype r] [DecidableEq r]
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    ((permutationChannel (a := a) n π⁻¹).prod (Channel.idChannel r)).applyState
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) =
      ω := by
  apply State.ext
  ext x y
  simp only [Channel.applyState]
  rw [permutationChannel_prod_id_map_apply]
  rw [permutationChannel_prod_id_map_apply]
  cases x with
  | mk xA xr =>
  cases y with
  | mk yA yr =>
    change ω.matrix (π • (π⁻¹ • xA), xr) (π • (π⁻¹ • yA), yr) =
      ω.matrix (xA, xr) (yA, yr)
    rw [← mul_smul, ← mul_smul]
    simp

/-- Under CKR post-selection covariance, applying a tensor-factor permutation
to the input-reference state preserves the channel-difference normalized trace
action.  One inequality is contraction through the covariance map; the reverse
uses the inverse permutation. -/
theorem postSelectionCovariantDifference_ancillaAction_permutation_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (π : Equiv.Perm (Fin n)) (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω) =
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  apply le_antisymm
  · exact postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
  · have hle := postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π⁻¹
      (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω)
    simpa [inputPermutation_inv_apply_permutation (a := a) (r := r) π ω] using hle

private theorem postSelectionCovariantDifference_labelExtension_action_eq
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputPermutationLabelExtension (a := a) (r := r)) =
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  rw [State.inputPermutationLabelExtension_channelDifference_action_traceNorm_eq_sum
    (a := a) (r := r) (b := b) Φ Ψ ω]
  have hterms :
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) =
        ∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) := by
    refine Finset.sum_congr rfl fun π _ => ?_
    simpa [c] using State.traceNorm_real_smul_eq
      (β := Prod b r) (c := c) hc
      (MatrixMap.kron Δ (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
  change (1 / 2 : ℝ) *
      (∑ π : Equiv.Perm (Fin n),
        traceNorm
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ •
            MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) =
    (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix)
  rw [hterms]
  have hpermTrace :
      ∀ π : Equiv.Perm (Fin n),
        traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map
            ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) =
        traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) := by
    intro π
    have h := postSelectionCovariantDifference_ancillaAction_permutation_eq
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
    dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction, Δ] at h
    nlinarith
  calc
    (1 / 2 : ℝ) *
        (∑ π : Equiv.Perm (Fin n),
          c * traceNorm
            (MatrixMap.kron Δ (Channel.idChannel r).map
              ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) ) =
        (1 / 2 : ℝ) *
          (∑ π : Equiv.Perm (Fin n),
            c * traceNorm
              (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix)) := by
          congr 1
          refine Finset.sum_congr rfl fun π _ => ?_
          rw [hpermTrace π]
    _ = (1 / 2 : ℝ) * traceNorm
          (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- A mixed input-reference state is controlled by the canonical pure extension
obtained by purifying the whole input-reference system.  The proof is the
finite-dimensional data-processing step: the mixed action is the partial trace
of the pure-extension action, and partial trace contracts trace norm. -/
private theorem inputReferenceAction_le_canonicalExtension
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let E := Prod (QIT.TensorPower a n) r
  let Y : CMatrix (Prod E (Prod b r)) :=
    MatrixMap.kron (Channel.idChannel E).map
      (MatrixMap.kron Δ (Channel.idChannel r).map)
      ω.canonicalPurification.state.matrix
  let Z : CMatrix (Prod b (Prod r E)) :=
    MatrixMap.kron Δ (Channel.idChannel (Prod r E)).map
      (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.matrix
  have hpt :
      partialTraceA (a := E) (b := Prod b r) Y =
        MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix := by
    calc
      partialTraceA (a := E) (b := Prod b r) Y =
          MatrixMap.kron Δ (Channel.idChannel r).map
            (partialTraceA (a := E) (b := E)
              ω.canonicalPurification.state.matrix) := by
            simpa [Y, E] using
              MatrixMap.partialTraceA_kron_idChannel_left
                (a := E) (c := E) (d := Prod b r)
                (MatrixMap.kron Δ (Channel.idChannel r).map)
                ω.canonicalPurification.state.matrix
      _ = MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix := by
            have hp : partialTraceA (a := E) (b := E)
                ω.canonicalPurification.state.matrix = ω.matrix := by
              exact PureVector.partialTraceA_state_matrix_eq_of_purifies
                ω.canonicalPurification_purifies
            rw [hp]
  have hreindex :
      Z =
        Y.submatrix
          (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
          (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm := by
    ext x y
    simp [Z, Y, State.inputReferenceCanonicalExtension,
      State.extensionPurificationInputEquiv, State.extensionPurificationOutputEquiv,
      PureVector.reindex_state, State.reindex,
      MatrixMap.kron_idChannel_apply_slice, MatrixMap.kron_idChannel_left_apply_slice]
  have htraceY : traceNorm Y = traceNorm Z := by
    rw [hreindex]
    symm
    exact traceNorm_submatrix_equiv
      (State.extensionPurificationOutputEquiv (a := a) (r := r) (b := b) (n := n)).symm
      Y
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron Δ (Channel.idChannel r).map ω.matrix) ≤
    (1 / 2 : ℝ) * traceNorm Z
  rw [← hpt]
  calc
    (1 / 2 : ℝ) * traceNorm (partialTraceA (a := E) (b := Prod b r) Y)
        ≤ (1 / 2 : ℝ) * traceNorm Y :=
          mul_le_mul_of_nonneg_left
            (traceNorm_partialTraceA_le_matrix (a := E) (b := Prod b r) Y)
            (by norm_num)
    _ = (1 / 2 : ℝ) * traceNorm Z := by rw [htraceY]

/-- The input marginal of the canonical pure extension of an input-reference
state is the original input marginal. -/
private theorem inputReferenceCanonicalExtension_marginalA
    {r : Type x} [Fintype r] [DecidableEq r]
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (ω.inputReferenceCanonicalExtension (a := a) (r := r)).state.marginalA =
      ω.marginalA := by
  apply State.ext
  ext i j
  have hp : partialTraceA (a := Prod (QIT.TensorPower a n) r)
      (b := Prod (QIT.TensorPower a n) r)
      ω.canonicalPurification.state.matrix = ω.matrix := by
    exact PureVector.partialTraceA_state_matrix_eq_of_purifies
      ω.canonicalPurification_purifies
  simp only [State.inputReferenceCanonicalExtension, State.marginalA, partialTraceB,
    PureVector.reindex_state, State.reindex, PureVector.state_matrix,
    rankOneMatrix_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun xr _ => ?_
  have hpij := congrFun (congrFun hp (i, xr)) (j, xr)
  simpa [partialTraceA, State.extensionPurificationInputEquiv] using hpij

/-- Swapping the canonical purification puts the purified system in the input
position, whose marginal is the original state. -/
private theorem canonicalPurification_reindex_prodComm_marginalA
    {α : Type v} [Fintype α] [DecidableEq α] (ρ : State α) :
    (ρ.canonicalPurification.reindex (Equiv.prodComm α α)).state.marginalA = ρ := by
  apply State.ext
  ext i j
  have hp : partialTraceA (a := α) (b := α)
      ρ.canonicalPurification.state.matrix = ρ.matrix := by
    exact PureVector.partialTraceA_state_matrix_eq_of_purifies
      ρ.canonicalPurification_purifies
  have hpij := congrFun (congrFun hp i) j
  simpa [State.marginalA, partialTraceB, partialTraceA,
    PureVector.reindex_state, State.reindex] using hpij

/-- Averaging an input-reference state over input tensor-factor permutations
does not increase the post-selection covariant channel-difference action. -/
theorem postSelectionCovariantDifference_ancillaAction_inputPermutationTwirling_le
    {r : Type x} [Fintype r] [DecidableEq r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ω.inputPermutationTwirling (a := a) (r := r)) ≤
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω := by
  classical
  let c : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        (((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
          (((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) ≤
    (1 / 2 : ℝ) * traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix)
  rw [map_smul, map_sum]
  have hsmul : traceNorm (((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) ≤
      c * traceNorm (∑ π : Equiv.Perm (Fin n),
      MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) :=
    traceNorm_real_smul_le hc _
  have hsum := traceNorm_sum_le_sum_traceNorm (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun π => MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
      ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
  have hterms : (∑ π : Equiv.Perm (Fin n), traceNorm
      (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
        ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)) ≤
      ∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix)) := by
    refine Finset.sum_le_sum fun π _ => ?_
    have h := postSelectionCovariantDifference_ancillaAction_permutation_le
      (a := a) (b := b) (r := r) Φ Ψ hcov π ω
    dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction] at h
    nlinarith [h]
  have hcard_ne : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin n)) ≠ 0)
  calc
    (1 / 2 : ℝ) * traceNorm
      ((c : ℂ) • ∑ π : Equiv.Perm (Fin n),
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))
        ≤ (1 / 2 : ℝ) * (c * traceNorm (∑ π : Equiv.Perm (Fin n),
        MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix))) :=
          mul_le_mul_of_nonneg_left hsmul (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map
          ((((permutationChannel (a := a) n π).prod (Channel.idChannel r)).applyState ω).matrix)))) := by
          gcongr
    _ ≤ (1 / 2 : ℝ) * (c * (∑ π : Equiv.Perm (Fin n), traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix))) := by
          gcongr
    _ = (1 / 2 : ℝ) * traceNorm
        (MatrixMap.kron (MatrixMap.channelDifference Φ Ψ) (Channel.idChannel r).map ω.matrix) := by
          simp [c, Finset.sum_const, nsmul_eq_mul, hcard_ne]

/-- Supported symmetric input-reference states are controlled by the CKR
purified post-selection reference action, with the exact profile-count factor.

This is the extractpart-to-action bridge: it applies the concrete
trace-effect extraction map from CKR `extractpart`, commutes the
channel-difference action past that extraction, and then uses
trace-nonincreasing CP contraction. -/
private theorem postSelection_supportedInputReferenceAction_le_profile_count_purified
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ρ : State (QIT.TensorPower (Prod a a) n))
    (hρ : ρ.SupportedOnSymmetricSubspace (a := Prod a a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (ρ.reindex (tensorPowerProdEquiv a a n)) ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Δ : MatrixMap (QIT.TensorPower a n) b := MatrixMap.channelDifference Φ Ψ
  let gR : ℝ := Fintype.card (TensorPowerProfile (Prod a a) n)
  let E : CMatrix (ckrPurifyingRegister a n) :=
    ρ.ckrProfileCoordinateEffect (a := a)
  let T : MatrixMap (ckrPurifyingRegister a n) PUnit.{1} :=
    MatrixMap.traceEffectToUnit E
  let H0 : CMatrix (Prod b (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))) :=
    (MatrixMap.kron Δ
      (Channel.idChannel (Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))).map)
      (postSelectionPurifiedReferenceState (a := a) n).matrix
  let H : CMatrix (Prod (Prod b (QIT.TensorPower a n)) (ckrPurifyingRegister a n)) :=
    assocRightMatrix H0
  have hEpos : E.PosSemidef := by
    simpa [E] using ρ.ckrProfileCoordinateEffect_posSemidef (a := a)
  have hT : T.TraceNonincreasingCP := by
    simpa [T, E] using
      ρ.ckrProfileCoordinateEffect_traceNonincreasingCP (a := a) hρ
  have hExtract := ρ.ckr_extractpart_profile_count_traceEffect (a := a) hρ
  have hActionEq :
      MatrixMap.kron Δ (Channel.idChannel (QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).matrix =
        (gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H) := by
    have hReindex :
        (ρ.reindex (tensorPowerProdEquiv a a n)).matrix =
          (gR : ℂ) •
            (dropRightUnitMatrix
              ((MatrixMap.kron
                  (Channel.idChannel (QIT.TensorPower (Prod a a) n)).map T)
                (ckrPurifiedReferenceState (a := a) n).matrix)).submatrix
              (tensorPowerProdEquiv a a n).symm
              (tensorPowerProdEquiv a a n).symm := by
      rw [State.reindex_matrix, hExtract]
      ext i j
      simp [Matrix.smul_apply, gR, T, E]
      left
      rfl
    rw [hReindex, map_smul]
    congr 1
    simpa [Δ, T, E, H, H0] using
      (dropRightUnitMatrix_action_traceEffectToUnit_commute
        (a := a) (n := n) (b := b) Δ (E := E) hEpos).symm
  have hH0Herm : H0.IsHermitian := by
    simpa [H0, Δ] using
      MatrixMap.channelDifference_kron_id_apply_isHermitian
        (a := QIT.TensorPower a n) (b := b)
        (r := Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))
        Φ Ψ (postSelectionPurifiedReferenceState (a := a) n)
  have hH0tr : H0.trace = 0 := by
    simpa [H0, Δ] using
      MatrixMap.channelDifference_kron_id_apply_trace_eq_zero
        (a := QIT.TensorPower a n) (b := b)
        (r := Prod (QIT.TensorPower a n) (ckrPurifyingRegister a n))
        Φ Ψ (postSelectionPurifiedReferenceState (a := a) n)
  have hHHerm : H.IsHermitian := by
    simpa [H] using assocRightMatrix_isHermitian hH0Herm
  have hHtr : H.trace = 0 := by
    simpa [H, hH0tr] using trace_assocRightMatrix H0
  have hContract :
      traceNorm
          (dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H)) ≤
        traceNorm H :=
    traceNorm_dropRightUnitMatrix_kron_id_le_of_traceNonincreasingCP
      (α := Prod b (QIT.TensorPower a n)) (β := ckrPurifyingRegister a n)
      hT hHHerm hHtr
  have hg_nonneg : 0 ≤ gR := by
    dsimp [gR]
    exact Nat.cast_nonneg _
  dsimp [MatrixMap.ancillaNormalizedTraceAction, MatrixMap.normalizedTraceAction]
  change (1 / 2 : ℝ) *
      traceNorm
        (MatrixMap.kron Δ (Channel.idChannel (QIT.TensorPower a n)).map
          (ρ.reindex (tensorPowerProdEquiv a a n)).matrix) ≤
    gR * ((1 / 2 : ℝ) * traceNorm H0)
  rw [hActionEq]
  calc
    (1 / 2 : ℝ) *
        traceNorm ((gR : ℂ) •
          dropRightUnitMatrix
            ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H))
        ≤ (1 / 2 : ℝ) *
            (gR * traceNorm
              (dropRightUnitMatrix
                ((MatrixMap.kron (Channel.idChannel (Prod b (QIT.TensorPower a n))).map T) H))) :=
          mul_le_mul_of_nonneg_left
            (traceNorm_real_smul_le hg_nonneg _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (gR * traceNorm H) := by
          gcongr
    _ = gR * ((1 / 2 : ℝ) * traceNorm H0) := by
          rw [traceNorm_assocRightMatrix H0]
          ring

/-- Pure input-reference states whose input marginal is permutation-invariant
are controlled by the CKR purified post-selection reference action.  The only
remaining step for the full CKR diamond theorem is the source's reduction from
arbitrary pure inputs to this invariant-marginal situation. -/
theorem postSelection_pureInputReferenceAction_le_profile_count_of_marginalA_invariant
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (Ω : PureVector (Prod (QIT.TensorPower a n) (QIT.TensorPower a n)))
    (hInv : Ω.state.marginalA.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  have hcanon :=
    Ω.channelDifference_normalizedAction_le_canonicalOfMarginalA Φ Ψ
  have hsup :=
    postSelection_supportedInputReferenceAction_le_profile_count_purified
      (a := a) (n := n) (b := b) Φ Ψ
      Ω.state.marginalA.inputCanonicalTensorPowerPurificationState
      (State.inputCanonicalTensorPowerPurification_supported_of_invariant
        (a := a) hInv)
  calc
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (Ω.state.marginalA.canonicalPurification.state.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))) :=
          hcanon
    _ ≤ (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
          simpa [State.inputCanonicalTensorPowerPurificationState_reindex_tensorPowerProdEquiv]
            using hsup

private theorem inputReferenceAction_le_profile_count_of_invariantMarginal
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (ω : State (Prod (QIT.TensorPower a n) r))
    (hInv : ω.marginalA.IsPermutationInvariant (a := a)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  classical
  let Ω : PureVector
      (Prod (QIT.TensorPower a n)
        (Prod r (Prod (QIT.TensorPower a n) r))) :=
    ω.inputReferenceCanonicalExtension (a := a) (r := r)
  have hExt :=
    inputReferenceAction_le_canonicalExtension (a := a) (n := n) (b := b)
      (r := r) Φ Ψ ω
  have hcard :
      Fintype.card (QIT.TensorPower a n) ≤
        Fintype.card (Prod r (Prod (QIT.TensorPower a n) r)) := by
    have hrpos : 0 < Fintype.card r := Fintype.card_pos_iff.mpr inferInstance
    have hmulpos : 0 < Fintype.card r * Fintype.card r := Nat.mul_pos hrpos hrpos
    have hbase :
        Fintype.card (QIT.TensorPower a n) ≤
          Fintype.card (QIT.TensorPower a n) * (Fintype.card r * Fintype.card r) :=
      Nat.le_mul_of_pos_right _ hmulpos
    simpa [Fintype.card_prod, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hbase
  have hCan :=
    Ω.channelDifference_normalizedAction_le_canonicalOfMarginalA_of_card_le
      Φ Ψ hcard
  have hCan' :
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction Ω.state ≤
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (ω.marginalA.canonicalPurification.reindex
            (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state := by
    simpa [Ω, inputReferenceCanonicalExtension_marginalA (a := a) (n := n) (r := r) ω]
      using hCan
  have hPureInv :
      State.IsPermutationInvariant
        (((ω.marginalA.canonicalPurification.reindex
          (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))).state).marginalA)
        (a := a) := by
    rw [canonicalPurification_reindex_prodComm_marginalA]
    exact hInv
  have hPure :=
    postSelection_pureInputReferenceAction_le_profile_count_of_marginalA_invariant
      (a := a) (n := n) (b := b) Φ Ψ
      (ω.marginalA.canonicalPurification.reindex
        (Equiv.prodComm (QIT.TensorPower a n) (QIT.TensorPower a n))) hPureInv
  exact hExt.trans (hCan'.trans hPure)

private theorem postSelection_labelExtensionAction_le_profile_count
    [Nonempty a] {r : Type x} [Fintype r] [DecidableEq r] [Nonempty r]
    (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) r)) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  have hlabel :=
    postSelectionCovariantDifference_labelExtension_action_eq
      (a := a) (n := n) (b := b) (r := r) Φ Ψ hcov ω
  have hbound :=
    inputReferenceAction_le_profile_count_of_invariantMarginal
      (a := a) (n := n) (b := b)
      (r := Prod r (Equiv.Perm (Fin n))) Φ Ψ
      (ω.inputPermutationLabelExtension (a := a) (r := r))
      (State.inputPermutationLabelExtension_marginalA_isPermutationInvariant
        (a := a) (r := r) ω)
  exact hlabel ▸ hbound

/-- CKR mixed input-reference reduction: under post-selection covariance, every
input-reference state is bounded by the purified post-selection reference
action with the exact profile-count factor. -/
theorem postSelection_inputReferenceAction_le_profile_count
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ)
    (ω : State (Prod (QIT.TensorPower a n) (QIT.TensorPower a n))) :
    (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction ω ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  classical
  letI : Nonempty (QIT.TensorPower a n) := QIT.TensorPower.nonempty (a := a) n
  exact postSelection_labelExtensionAction_le_profile_count
    (a := a) (n := n) (b := b)
    (r := QIT.TensorPower a n) Φ Ψ hcov ω

/-- CKR finite-dimensional post-selection theorem in source-shaped diamond
trace-distance form, with the exact profile-count factor. -/
theorem postSelection_diamondTraceDistance_le_profile_count
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  classical
  refine Channel.diamondTraceDistance_le_of_inputReferenceBound
    (a := QIT.TensorPower a n) (b := b) (Φ := Φ) (Ψ := Ψ)
    (ε := (Fintype.card (TensorPowerProfile (Prod a a) n) : ℝ) *
      (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
        (postSelectionPurifiedReferenceState (a := a) n)) ?_
  intro ω
  rw [Channel.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact postSelection_inputReferenceAction_le_profile_count
    (a := a) (n := n) (b := b) Φ Ψ hcov ω

/-- CKR post-selection theorem with the equivalent binomial symmetric-dimension
factor. -/
theorem postSelection_diamondTraceDistance_le_choose
    [Nonempty a] (Φ Ψ : Channel (QIT.TensorPower a n) b)
    (hcov : PostSelectionCovariantDifference (a := a) (n := n) Φ Ψ) :
    Φ.diamondTraceDistance Ψ ≤
      (Nat.choose (n + Fintype.card (Prod a a) - 1) n : ℝ) *
        (MatrixMap.channelDifference Φ Ψ).ancillaNormalizedTraceAction
          (postSelectionPurifiedReferenceState (a := a) n) := by
  simpa [tensorPowerProfile_card_eq_choose (a := Prod a a) n] using
    postSelection_diamondTraceDistance_le_profile_count
      (a := a) (n := n) (b := b) Φ Ψ hcov

/-- To bound the source-shaped finite-dimensional diamond trace distance it is
enough to bound the channel-difference action on pure input-reference states.
This packages the spectral decomposition and convexity bridge for later CKR
post-selection assembly. -/
theorem diamondTraceDistance_le_of_pureInputReferenceBound [Nonempty a]
    {Φ Ψ : Channel a b} {ε : ℝ}
    (h : ∀ Ω : PureVector (Prod a a),
      MatrixMap.ancillaNormalizedTraceAction (MatrixMap.channelDifference Φ Ψ) Ω.state ≤ ε) :
    Φ.diamondTraceDistance Ψ ≤ ε := by
  refine Channel.diamondTraceDistance_le_of_inputReferenceBound (a := a) (b := b)
    (Φ := Φ) (Ψ := Ψ) (ε := ε) ?_
  intro ω
  rw [Channel.ancillaChannelTraceDistance_eq_channelDifferenceAction]
  exact MatrixMap.ancillaNormalizedTraceAction_le_of_forall_pure_bound
    (MatrixMap.channelDifference Φ Ψ) ω h

end Channel

namespace SubnormalizedState

variable {n : ℕ}

/-- A subnormalized state is supported on the symmetric tensor-power subspace
when its matrix is bounded by the symmetric projection. -/
def SupportedOnSymmetricSubspace (ρ : SubnormalizedState (TensorPower a n)) : Prop :=
  ρ.matrix ≤ symmetricProjectionMatrix (a := a) n

theorem supportedOnSymmetricSubspace_iff
    (ρ : SubnormalizedState (TensorPower a n)) :
    ρ.SupportedOnSymmetricSubspace (a := a) ↔
      ρ.matrix ≤ symmetricProjectionMatrix (a := a) n := by
  rfl

end SubnormalizedState

namespace State

variable {n : ℕ}

/-- Project a tensor-power state onto the symmetric subspace on both sides:
`P_sym ρ P_sym`. This matrix is generally subnormalized. -/
def symmetricProjectionSandwichMatrix (ρ : State (TensorPower a n)) :
    CMatrix (TensorPower a n) :=
  symmetricProjectionMatrix (a := a) n * ρ.matrix * symmetricProjectionMatrix (a := a) n

@[simp]
theorem symmetricProjectionSandwichMatrix_eq (ρ : State (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) =
      symmetricProjectionMatrix (a := a) n * ρ.matrix *
        symmetricProjectionMatrix (a := a) n := rfl

/-- The symmetric projection sandwich `P_sym ρ P_sym` is positive semidefinite. -/
theorem symmetricProjectionSandwichMatrix_posSemidef
    (ρ : State (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichMatrix (a := a)).PosSemidef := by
  have h := ρ.pos.conjTranspose_mul_mul_same (symmetricProjectionMatrix (a := a) n)
  simpa [symmetricProjectionSandwichMatrix, symmetricProjectionMatrix_conjTranspose]
    using h

/-- The trace of `P_sym ρ P_sym` is at most one. -/
theorem symmetricProjectionSandwichMatrix_trace_re_le_one
    (ρ : State (TensorPower a n)) :
    ((ρ.symmetricProjectionSandwichMatrix (a := a)).trace).re ≤ 1 := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have htrace_le' :
      ((ρ.matrix * P).trace).re ≤ ((ρ.matrix * 1).trace).re :=
    cMatrix_trace_mul_le_of_le ρ.pos (symmetricProjectionMatrix_le_one (a := a) n)
  have htrace_le : ((ρ.matrix * P).trace).re ≤ ρ.matrix.trace.re := by
    simpa [P, Matrix.mul_one] using htrace_le'
  have hcyc :
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace = (ρ.matrix * P).trace := by
    calc
      (ρ.symmetricProjectionSandwichMatrix (a := a)).trace =
          (P * ρ.matrix * P).trace := rfl
      _ = (ρ.matrix * (P * P)).trace := by
          calc
            (P * ρ.matrix * P).trace = ((P * ρ.matrix) * P).trace := by
              rw [Matrix.mul_assoc]
            _ = (P * (P * ρ.matrix)).trace := by rw [Matrix.trace_mul_comm]
            _ = ((P * P) * ρ.matrix).trace := by rw [← Matrix.mul_assoc]
            _ = (ρ.matrix * (P * P)).trace := by rw [Matrix.trace_mul_comm]
      _ = (ρ.matrix * P).trace := by
          rw [show P * P = P by
            exact symmetricProjectionMatrix_idempotent (a := a) n]
  rw [hcyc]
  rw [ρ.trace_eq_one] at htrace_le
  norm_num at htrace_le
  exact htrace_le

/-- The projected matrix `P_sym ρ P_sym` is bounded by `P_sym`; equivalently,
the projected subnormalized state is automatically supported in the symmetric
subspace. -/
theorem symmetricProjectionSandwichMatrix_le_symmetricProjection
    (ρ : State (TensorPower a n)) :
    ρ.symmetricProjectionSandwichMatrix (a := a) ≤
      symmetricProjectionMatrix (a := a) n := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.matrix * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [symmetricProjectionSandwichMatrix, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc] using hconj

/-- The symmetric projection sandwich as a subnormalized state. -/
def symmetricProjectionSandwichSubnormalizedState
    (ρ : State (TensorPower a n)) :
    SubnormalizedState (TensorPower a n) where
  matrix := ρ.symmetricProjectionSandwichMatrix (a := a)
  pos := ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)
  trace_le_one := ρ.symmetricProjectionSandwichMatrix_trace_re_le_one (a := a)

@[simp]
theorem symmetricProjectionSandwichSubnormalizedState_matrix
    (ρ : State (TensorPower a n)) :
    (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)).matrix =
      ρ.symmetricProjectionSandwichMatrix (a := a) := rfl

/-- The symmetric projection sandwich subnormalized state is supported on the
symmetric tensor-power subspace. -/
theorem symmetricProjectionSandwichSubnormalizedState_supportedOnSymmetricSubspace
    (ρ : State (TensorPower a n)) :
    SubnormalizedState.SupportedOnSymmetricSubspace
      (a := a) (ρ.symmetricProjectionSandwichSubnormalizedState (a := a)) :=
  ρ.symmetricProjectionSandwichMatrix_le_symmetricProjection (a := a)

private theorem symmetricProjectionSandwichMatrix_fixed
    (ρ : State (TensorPower a n)) :
    symmetricProjectionMatrix (a := a) n *
        ρ.symmetricProjectionSandwichMatrix (a := a) *
        symmetricProjectionMatrix (a := a) n =
      ρ.symmetricProjectionSandwichMatrix (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  calc
    P * ρ.symmetricProjectionSandwichMatrix (a := a) * P =
        P * (P * ρ.matrix * P) * P := rfl
    _ = P * ρ.matrix * P := by
        have hP2 : P * P = P := symmetricProjectionMatrix_idempotent (a := a) n
        calc
          P * (P * ρ.matrix * P) * P = (P * P) * ρ.matrix * (P * P) := by
            noncomm_ring
          _ = P * ρ.matrix * P := by rw [hP2]

private theorem supportedOnSymmetricSubspace_of_projection_fixed
    (ρ : State (TensorPower a n))
    (hfixed : symmetricProjectionMatrix (a := a) n * ρ.matrix *
        symmetricProjectionMatrix (a := a) n = ρ.matrix) :
    ρ.SupportedOnSymmetricSubspace (a := a) := by
  let P : CMatrix (TensorPower a n) := symmetricProjectionMatrix (a := a) n
  have hconj : P.conjTranspose * ρ.matrix * P ≤ P.conjTranspose * 1 * P :=
    star_left_conjugate_le_conjugate (matrix_le_one ρ) P
  simpa [SupportedOnSymmetricSubspace, P, symmetricProjectionMatrix_conjTranspose,
    symmetricProjectionMatrix_idempotent, Matrix.mul_assoc, hfixed] using hconj

/-- Normalize the symmetric projection sandwich when its trace is positive. -/
def symmetricProjectionNormalizedState
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    State (TensorPower a n) where
  matrix := (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
    ρ.symmetricProjectionSandwichMatrix (a := a)
  pos := (ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a)).smul
    (by exact_mod_cast inv_nonneg.mpr htrace.le)
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_im :
        (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.im = 0 :=
      (Matrix.PosSemidef.trace_nonneg
        (ρ.symmetricProjectionSandwichMatrix_posSemidef (a := a))).2.symm
    have htrace_complex :
        (ρ.symmetricProjectionSandwichMatrix (a := a)).trace =
          ((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using htrace_im
    rw [htrace_complex]
    let t : ℝ := (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re
    have ht_ne : t ≠ 0 := ne_of_gt htrace
    change ((t : ℂ)⁻¹ • (t : ℂ)) = 1
    rw [Algebra.smul_def]
    have htc_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht_ne
    simpa using inv_mul_cancel₀ htc_ne

@[simp]
theorem symmetricProjectionNormalizedState_matrix
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).matrix =
      (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
        ρ.symmetricProjectionSandwichMatrix (a := a) := rfl

/-- The normalized symmetric projection state is supported on the symmetric
tensor-power subspace. -/
theorem symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    State.SupportedOnSymmetricSubspace
      (a := a) (ρ.symmetricProjectionNormalizedState (a := a) htrace) := by
  apply supportedOnSymmetricSubspace_of_projection_fixed
  rw [symmetricProjectionNormalizedState_matrix]
  calc
    symmetricProjectionMatrix (a := a) n *
        ((((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          ρ.symmetricProjectionSandwichMatrix (a := a)) *
        symmetricProjectionMatrix (a := a) n =
        (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          (symmetricProjectionMatrix (a := a) n *
            ρ.symmetricProjectionSandwichMatrix (a := a) *
            symmetricProjectionMatrix (a := a) n) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = (((ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)⁻¹ : ℂ) •
          ρ.symmetricProjectionSandwichMatrix (a := a) := by
          rw [symmetricProjectionSandwichMatrix_fixed]

/-- The normalized symmetric projection state can be used directly in the
exact profile-count post-selection domination theorem. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    [Nonempty a] (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_of_supported
    (a := a)
    (ρ.symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
      (a := a) htrace)

/-- Polynomial-factor post-selection domination for the normalized symmetric
projection state. -/
theorem matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    [Nonempty a] (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re) :
    (ρ.symmetricProjectionNormalizedState (a := a) htrace).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (symmetricProjectionReferenceState (a := a) n) :=
  matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_supported
    (a := a)
    (ρ.symmetricProjectionNormalizedState_supportedOnSymmetricSubspace
      (a := a) htrace)

/-- Exact profile-count channel-output post-selection domination for the
normalized symmetric projection state. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Polynomial-factor channel-output post-selection domination for the
normalized symmetric projection state. -/
theorem matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  matrixDominatedBy_applyChannel Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- State-level post-selection theorem with the constructed normalized
projection state as input. This removes the need to supply a separate support
hypothesis. -/
theorem stateLevelPostSelectionBound_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      ((n + 1) ^ Fintype.card a : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
    (a := a) htrace Φ

/-- Exact profile-count state-level post-selection theorem with the constructed
normalized projection state as input. -/
theorem stateLevelPostSelectionBound_profile_count_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).MatrixDominatedBy
      (Fintype.card (TensorPowerProfile a n) : ℝ)
      (Φ.applyState (symmetricProjectionReferenceState (a := a) n)) :=
  ρ.matrixDominatedBy_applyChannel_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
    (a := a) htrace Φ

/-- Polynomial-factor trace-distance post-selection theorem with the
constructed normalized projection state as input. -/
theorem stateLevelPostSelectionTraceDistanceBound_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ
      (ρ.symmetricProjectionNormalizedState (a := a) htrace)
      (symmetricProjectionReferenceState (a := a) n)
      (((n + 1) ^ Fintype.card a : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_pow_succ_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Exact profile-count trace-distance post-selection theorem with the
constructed normalized projection state as input. -/
theorem stateLevelPostSelectionTraceDistanceBound_profile_count_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    ChannelOutputTraceDistanceBound Φ
      (ρ.symmetricProjectionNormalizedState (a := a) htrace)
      (symmetricProjectionReferenceState (a := a) n)
      ((Fintype.card (TensorPowerProfile a n) : ℝ) - 1) :=
  channelOutputTraceDistanceBound_of_matrixDominatedBy Φ
    (ρ.matrixDominatedBy_symmetricProjectionReferenceState_of_symmetricProjectionNormalizedState
      (a := a) htrace)

/-- Difference-matrix form of the polynomial post-selection domination theorem
for the constructed normalized projection state. -/
theorem stateLevelPostSelectionDifference_posSemidef_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    ((((n + 1) ^ Fintype.card a : ℝ) : ℂ) •
        (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).matrix -
      (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).matrix).PosSemidef := by
  have h :=
    ρ.stateLevelPostSelectionBound_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

/-- Difference-matrix form of the exact profile-count post-selection domination
theorem for the constructed normalized projection state. -/
theorem stateLevelPostSelectionDifference_profile_count_posSemidef_of_symmetricProjectionNormalizedState
    {b : Type w} [Fintype b] [DecidableEq b] [Nonempty a]
    (ρ : State (TensorPower a n))
    (htrace : 0 < (ρ.symmetricProjectionSandwichMatrix (a := a)).trace.re)
    (Φ : Channel (TensorPower a n) b) :
    (((Fintype.card (TensorPowerProfile a n) : ℝ) : ℂ) •
        (Φ.applyState (symmetricProjectionReferenceState (a := a) n)).matrix -
      (Φ.applyState (ρ.symmetricProjectionNormalizedState (a := a) htrace)).matrix).PosSemidef := by
  have h :=
    ρ.stateLevelPostSelectionBound_profile_count_of_symmetricProjectionNormalizedState
      (a := a) htrace Φ
  dsimp [MatrixDominatedBy] at h
  rwa [Matrix.le_iff] at h

end State

namespace FiniteIidMixture

variable {n : ℕ} (M : FiniteIidMixture ι a n)

/-- A finite IID mixture state is dominated by itself with factor `1`. -/
theorem state_isDominatedBy_self :
    M.state.IsDominatedByFiniteIidMixture 1 M :=
  State.matrixDominatedBy_refl M.state

/-- A finite IID mixture state is dominated by itself with any factor at least
`1`. -/
theorem state_isDominatedBy_self_mono_factor {c : ℝ} (hc : 1 ≤ c) :
    M.state.IsDominatedByFiniteIidMixture c M :=
  State.isDominatedByFiniteIidMixture_mono_factor
    (M.state_isDominatedBy_self) hc

/-- Matrix form of the image of a finite IID mixture under a channel. -/
theorem applyChannel_state_matrix {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) :
    (Φ.applyState M.state).matrix =
      ∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix := by
  change Φ.map M.state.matrix =
    ∑ i, (M.probs i) • Φ.map ((M.states i).tensorPower n).matrix
  rw [M.state_matrix, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change Φ.map ((M.probs i : ℂ) • ((M.states i).tensorPower n).matrix) =
    (M.probs i : ℂ) • Φ.map ((M.states i).tensorPower n).matrix
  rw [map_smul]

/-- If every tensor-power component of a finite IID mixture is dominated by the
same target state with the same factor, then the whole mixture is dominated by
that target with the same factor. -/
theorem matrixDominatedBy_of_forall_tensorPower (τ : State (TensorPower a n)) (c : ℝ)
    (h : ∀ i, ((M.states i).tensorPower n).MatrixDominatedBy c τ) :
    M.state.MatrixDominatedBy c τ := by
  dsimp [State.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.matrix) - M.state.matrix).PosSemidef
  rw [M.state_matrix]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) = (c : ℂ) • τ.matrix := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) - ((M.states i).tensorPower n).matrix) := by
    calc
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) -
            (∑ i, (M.probs i) • ((M.states i).tensorPower n).matrix) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.matrix) -
            (M.probs i) • ((M.states i).tensorPower n).matrix) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) - ((M.states i).tensorPower n).matrix) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_sub]
  rw [hrewrite]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (h i).smul (NNReal.coe_nonneg (M.probs i))

/-- If each channel image of a tensor-power component is dominated by the same
target state with the same factor, then the channel image of the whole finite
IID mixture is dominated by that target. -/
theorem applyChannel_matrixDominatedBy_of_forall_tensorPower
    {b : Type w} [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) b) (τ : State b) (c : ℝ)
    (h : ∀ i, (Φ.applyState ((M.states i).tensorPower n)).MatrixDominatedBy c τ) :
    (Φ.applyState M.state).MatrixDominatedBy c τ := by
  dsimp [State.MatrixDominatedBy] at h ⊢
  change (((c : ℂ) • τ.matrix) - (Φ.applyState M.state).matrix).PosSemidef
  rw [M.applyChannel_state_matrix Φ]
  have hsum_coeff :
      (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) = (c : ℂ) • τ.matrix := by
    rw [← Finset.sum_smul]
    rw [M.weights_sum, one_smul]
  have hrewrite :
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) =
        ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) -
            (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
    calc
      ((c : ℂ) • τ.matrix) -
          (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) =
          (∑ i, (M.probs i) • ((c : ℂ) • τ.matrix)) -
            (∑ i, (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
            rw [hsum_coeff]
      _ = ∑ i, ((M.probs i) • ((c : ℂ) • τ.matrix) -
            (M.probs i) • (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i, (M.probs i) •
          (((c : ℂ) • τ.matrix) -
            (Φ.applyState ((M.states i).tensorPower n)).matrix) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [smul_sub]
  rw [hrewrite]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    (h i).smul (NNReal.coe_nonneg (M.probs i))

/-- If each channel image of a tensor-power component is dominated by the same
output finite IID mixture, then the channel image of the whole finite IID
mixture is dominated by that output mixture. -/
theorem applyChannel_isDominatedByFiniteIidMixture_of_forall_tensorPower
    {κ : Type x} {b : Type w} [Fintype κ] [Fintype b] [DecidableEq b]
    (Φ : Channel (TensorPower a n) (TensorPower b n))
    (N : FiniteIidMixture κ b n) (c : ℝ)
    (h : ∀ i, (Φ.applyState ((M.states i).tensorPower n)).IsDominatedByFiniteIidMixture c N) :
    (Φ.applyState M.state).IsDominatedByFiniteIidMixture c N :=
  M.applyChannel_matrixDominatedBy_of_forall_tensorPower Φ N.state c h

/-- If every tensor-power component of a finite IID mixture is dominated by the
same finite IID mixture, then the averaged mixture is dominated by it as well. -/
theorem isDominatedByFiniteIidMixture_of_forall_tensorPower
    (N : FiniteIidMixture ι a n) (c : ℝ)
    (h : ∀ i, ((M.states i).tensorPower n).IsDominatedByFiniteIidMixture c N) :
    M.state.IsDominatedByFiniteIidMixture c N :=
  M.matrixDominatedBy_of_forall_tensorPower N.state c h

/-- Componentwise domination by a finite IID mixture can be composed with
matrix domination of the target mixture state. -/
theorem matrixDominatedBy_trans_of_forall_tensorPower
    (N : FiniteIidMixture ι a n) (τ : State (TensorPower a n)) {c d : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ i, ((M.states i).tensorPower n).IsDominatedByFiniteIidMixture c N)
    (hNτ : N.state.MatrixDominatedBy d τ) :
    M.state.MatrixDominatedBy (c * d) τ :=
  State.matrixDominatedBy_trans hc
    (M.isDominatedByFiniteIidMixture_of_forall_tensorPower N c h) hNτ

end FiniteIidMixture

end

end QIT
