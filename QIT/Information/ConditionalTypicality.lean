/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Typicality
public import QIT.States.Product
public import QIT.Information.Entropy
public import QIT.Classical.CQState

/-!
# Conditionally-typical subspace projector

Spectral conditionally-typical projector for a non-iid product state
`⊗_i ρ_i`, the HSW object. The eigenvalue predicate centers at the
per-sequence entropy sum `Σ_i S(ρ_i)`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Eigenvalue typicality for the non-iid product state `⊗_i ρ_i`: `-log₂ μ`
lies within `n δ` of `Σ_i S(ρ_i)`, zero eigenvalues excluded. -/
def conditionallyTypicalEigenvalue {n : ℕ} (states : Fin n → State a) (δ μ : ℝ) : Prop :=
  0 < μ ∧ |(-log2 μ) - ∑ i, (states i).vonNeumann| ≤ (n : ℝ) * δ

/-- Spectral conditionally-typical projector for `⊗_i ρ_i`; eigenvalue
predicate centered at `Σ_i S(ρ_i)`. Source: [Wilde2011Qst, qit-notes.tex:28649-28672]. -/
def conditionallyTypicalSubspaceProjector {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    CMatrix (TensorPower a n) := by
  classical
  let τ := productState states
  exact spectralPredicateProjector τ.matrix τ.pos.isHermitian
    (fun i => conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i))

/-- Number of selected spectral directions, expressed as a real trace count. -/
def conditionallyTypicalSubspaceDimension {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then (1 : ℝ) else 0

/-- Spectral probability weight accepted by the conditionally-typical projector. -/
def conditionallyTypicalSpectralWeight {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then τ.pos.isHermitian.eigenvalues i else 0

/-- Spectral probability weight rejected by the conditionally-typical projector. -/
def conditionallyAtypicalSpectralWeight {n : ℕ} (states : Fin n → State a) (δ : ℝ) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    if ¬ conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
    then τ.pos.isHermitian.eigenvalues i else 0

/-- Second moment of the centered log-eigenvalue random variable for the
product state `⊗_i ρ_i`, centered at `Σ_i S(ρ_i)`. It is the finite
spectral-distribution quantity that feeds Chebyshev-style concentration
estimates; separate product-spectrum lemmas are needed to turn it into an
explicit variance bound. -/
def conditionalLogDeviationSecondMoment {n : ℕ} (states : Fin n → State a) : ℝ := by
  classical
  let τ := productState states
  exact ∑ i : TensorPower a n,
    let μ := τ.pos.isHermitian.eigenvalues i
    μ * (((-log2 μ) - ∑ j, (states j).vonNeumann) ^ 2)

/-- The conditionally-typical projector is positive semidefinite. -/
theorem conditionallyTypicalSubspaceProjector_posSemidef {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).PosSemidef := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_posSemidef _ _ _

/-- The conditionally-typical projector is Hermitian. -/
theorem conditionallyTypicalSubspaceProjector_isHermitian {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).IsHermitian :=
  (conditionallyTypicalSubspaceProjector_posSemidef states δ).1

/-- The conditionally-typical projector is idempotent. -/
theorem conditionallyTypicalSubspaceProjector_idempotent {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSubspaceProjector states δ *
      conditionallyTypicalSubspaceProjector states δ =
      conditionallyTypicalSubspaceProjector states δ := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_idempotent _ _ _

/-- The conditionally-typical projector is bounded by the identity effect. -/
theorem conditionallyTypicalSubspaceProjector_le_one {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSubspaceProjector states δ ≤ 1 := by
  classical
  unfold conditionallyTypicalSubspaceProjector
  exact spectralPredicateProjector_le_one _ _ _

/-- Eigenvalues of a non-iid product density matrix sum to one. -/
theorem productState_eigenvalue_sum {n : ℕ} (states : Fin n → State a) :
    ∑ i : TensorPower a n, (productState states).pos.isHermitian.eigenvalues i = 1 := by
  have hc :
      (∑ i : TensorPower a n,
          (((productState states).pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
    (productState states).pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans
      (productState states).trace_eq_one
  rw [← Complex.ofReal_sum] at hc
  exact Complex.ofReal_injective hc

/-- The conditionally-typical spectral weight is nonnegative. -/
theorem conditionallyTypicalSpectralWeight_nonneg {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    0 ≤ conditionallyTypicalSpectralWeight states δ := by
  classical
  set τ := productState states
  unfold conditionallyTypicalSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
  · simp only [hi]; exact τ.pos.eigenvalues_nonneg i
  · simp only [hi]; exact le_refl _

/-- The conditionally-atypical spectral weight is nonnegative. -/
theorem conditionallyAtypicalSpectralWeight_nonneg {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    0 ≤ conditionallyAtypicalSpectralWeight states δ := by
  classical
  set τ := productState states
  unfold conditionallyAtypicalSpectralWeight
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
  · simp only [hi]; exact le_refl _
  · simp only [hi]; exact τ.pos.eigenvalues_nonneg i

/-- The centered log-eigenvalue second moment of the product state is nonnegative. -/
theorem conditionalLogDeviationSecondMoment_nonneg {n : ℕ}
    (states : Fin n → State a) :
    0 ≤ conditionalLogDeviationSecondMoment states := by
  classical
  set τ := productState states
  unfold conditionalLogDeviationSecondMoment
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (τ.pos.eigenvalues_nonneg i) (sq_nonneg _)

/-- The conditionally-typical and conditionally-atypical spectral weights
partition the product state's total spectral weight. -/
theorem conditionallyTypicalSpectralWeight_add_atypical {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) :
    conditionallyTypicalSpectralWeight states δ +
      conditionallyAtypicalSpectralWeight states δ = 1 := by
  classical
  set τ := productState states
  unfold conditionallyTypicalSpectralWeight conditionallyAtypicalSpectralWeight
  rw [← Finset.sum_add_distrib]
  have hsum : ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i = 1 := by
    have hc :
        (∑ i : TensorPower a n,
            ((τ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) = 1 :=
      τ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans τ.trace_eq_one
    rw [← Complex.ofReal_sum] at hc
    exact Complex.ofReal_injective hc
  calc
    (∑ i : TensorPower a n,
        ((if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
          then τ.pos.isHermitian.eigenvalues i else 0) +
        if ¬ conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
          then τ.pos.isHermitian.eigenvalues i else 0)) =
        ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i := by
          apply Finset.sum_congr rfl
          intro i _
          split
          · rw [add_zero]
          · rw [zero_add]
    _ = 1 := hsum

/-- Finite spectral Chebyshev bridge for the conditionally-typical projector.

This is a genuine concentration-form estimate at the spectral-distribution
level: the conditionally-atypical spectral weight times `(n δ)^2` is controlled
by the centered second moment of the log-eigenvalues of the product state
`⊗_i ρ_i`, centered at `Σ_i S(ρ_i)`. -/
theorem conditionallyAtypicalSpectralWeight_mul_sq_le_logDeviationSecondMoment
    {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    conditionallyAtypicalSpectralWeight states δ * (((n : ℝ) * δ) ^ 2) ≤
      conditionalLogDeviationSecondMoment states := by
  classical
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  set τ := productState states
  unfold conditionallyAtypicalSpectralWeight conditionalLogDeviationSecondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  set μ := τ.pos.isHermitian.eigenvalues i with hμ_def
  set d := (-log2 μ) - ∑ j, (states j).vonNeumann with hd_def
  have hμ_nonneg : 0 ≤ μ := τ.pos.eigenvalues_nonneg i
  by_cases htyp : conditionallyTypicalEigenvalue states δ μ
  · -- typical: atypical contribution is 0; RHS μ*d^2 ≥ 0
    have h_rhs_nonneg : 0 ≤ μ * d ^ 2 := mul_nonneg hμ_nonneg (sq_nonneg d)
    have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
        * ((n : ℝ) * δ) ^ 2 = 0 := by
      have hnn : ¬ (¬ conditionallyTypicalEigenvalue states δ μ) := fun h => h htyp
      rw [if_neg hnn, zero_mul]
    rw [h_lhs]
    exact h_rhs_nonneg
  · by_cases hμ_pos : 0 < μ
    · -- atypical and μ > 0: |d| > n*δ, so (n*δ)^2 ≤ d^2, multiply by μ ≥ 0
      have hnotle : ¬ |d| ≤ (n : ℝ) * δ := by
        intro hle
        exact htyp ⟨hμ_pos, by simpa [d, μ] using hle⟩
      have hclt : (n : ℝ) * δ < |d| := lt_of_not_ge hnotle
      have hcabs : |(n : ℝ) * δ| ≤ |d| := by
        rw [abs_of_nonneg (le_of_lt hcpos)]
        exact le_of_lt hclt
      have hsq : ((n : ℝ) * δ) ^ 2 ≤ d ^ 2 := by
        have hs := sq_le_sq.mpr hcabs
        simpa [sq_abs] using hs
      have hmul := mul_le_mul_of_nonneg_left hsq hμ_nonneg
      have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
          * ((n : ℝ) * δ) ^ 2 = μ * ((n : ℝ) * δ) ^ 2 := by
        rw [if_pos htyp]
      rw [h_lhs]
      exact hmul
    · -- μ = 0: both sides 0 (μ * anything = 0)
      have hμ_zero : μ = 0 := le_antisymm (not_lt.mp hμ_pos) hμ_nonneg
      have h_lhs : (if ¬ conditionallyTypicalEigenvalue states δ μ then μ else 0)
          * ((n : ℝ) * δ) ^ 2 = 0 := by
        rw [if_pos htyp, hμ_zero, zero_mul]
      have h_rhs : μ * d ^ 2 = 0 := by rw [hμ_zero, zero_mul]
      rw [h_lhs, h_rhs]

/-- Division form of the finite spectral Chebyshev bridge. -/
theorem conditionallyAtypicalSpectralWeight_le_logDeviationSecondMoment_div_sq
    {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) :
    conditionallyAtypicalSpectralWeight states δ ≤
      conditionalLogDeviationSecondMoment states / (((n : ℝ) * δ) ^ 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < (n : ℝ) * δ := mul_pos hnR hδ
  have hc2pos : 0 < (((n : ℝ) * δ) ^ 2) := sq_pos_of_pos hcpos
  rw [le_div_iff₀ hc2pos]
  exact conditionallyAtypicalSpectralWeight_mul_sq_le_logDeviationSecondMoment
    states hn hδ

/-- pack-2: the conditionally-typical projector captures its own product state.
`Tr{Π_cond · (⊗_i ρ_i)} ≥ 1 − (secondMoment / (nδ)²)`.
Source: [Wilde2011Qst, qit-notes.tex:28704-28713]. -/
theorem conditionallyTypicalSubspaceProjector_ownCapture {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) (hn : 0 < n) (hδ : 0 < δ) :
    1 - conditionalLogDeviationSecondMoment states / ((n : ℝ) * δ) ^ 2
      ≤ conditionallyTypicalSpectralWeight states δ := by
  have hle := conditionallyAtypicalSpectralWeight_le_logDeviationSecondMoment_div_sq
    states hn hδ
  have hadd := conditionallyTypicalSpectralWeight_add_atypical states δ
  linarith

/-! ## pack-3: dimension bound

Each accepted eigenvalue `μ` of the product state `⊗_i ρ_i` satisfies the
typicality predicate, whose upper bound on `-log₂ μ` gives the eigenvalue
lower bound `μ ≥ 2^{-(Σ_i S(ρ_i) + n δ)}`. Since the accepted spectral weight
`Σ_{accepted} μ` is at most the total spectral weight `1`, the number of
accepted directions is bounded by `2^{Σ_i S(ρ_i) + n δ}`. This mirrors the
iid dimension argument: an eigenvalue lower bound together with a total
spectral weight of one bounds the count of selected directions. -/

/-- pack-3 (core): the conditionally-typical-subspace dimension satisfies
`Tr{Π_cond} ≤ 2^{Σ_i S(ρ_i) + n δ}`. This is a pure finite-spectral
estimate: it uses only the eigenvalue lower bound implied by the
typicality predicate and the fact that the product state's eigenvalues
sum to one. No entropy-additivity interface is required (the per-symbol
entropy sum `Σ_i S(ρ_i)` is already the center of the predicate).
Source: [Wilde2011Qst, qit-notes.tex:28715-28734]. -/
theorem conditionallyTypicalSubspaceProjector_dim_le {n : ℕ}
    (states : Fin n → State a) (δ : ℝ) (hδ : 0 < δ) :
    conditionallyTypicalSubspaceDimension states δ
      ≤ Real.rpow 2 (∑ i, (states i).vonNeumann + (n : ℝ) * δ) := by
  classical
  set τ := productState states
  set S := ∑ i, (states i).vonNeumann
  -- The product state's eigenvalues sum to one (total spectral weight).
  have hsum : ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i = 1 :=
    productState_eigenvalue_sum states
  -- The base 2^(ΣS + nδ) is strictly positive.
  have hbase_pos : 0 < Real.rpow 2 (S + (n : ℝ) * δ) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hl2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- For each accepted eigenvalue μ: μ ≥ 2^{-(ΣS + nδ)}, equivalently
  -- 1 ≤ μ * 2^{ΣS + nδ}.
  have hkey : ∀ i : TensorPower a n,
      conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i) →
        (1 : ℝ) ≤ τ.pos.isHermitian.eigenvalues i *
          Real.rpow 2 (S + (n : ℝ) * δ) := by
    intro i htyp
    obtain ⟨hμ_pos, habs⟩ := htyp
    set μ := τ.pos.isHermitian.eigenvalues i
    -- From the predicate: -log2 μ - S ≤ nδ, hence -log2 μ ≤ S + nδ.
    have hnegle : -log2 μ - S ≤ (n : ℝ) * δ := (abs_le.mp habs).2
    have hlog_le : -log2 μ ≤ S + (n : ℝ) * δ := by linarith
    -- Convert the log2 bound into a Real.log bound:
    -- Real.log μ ≥ -(S + nδ) · Real.log 2.
    have hlogμ_ge : -(S + (n : ℝ) * δ) * Real.log 2 ≤ Real.log μ := by
      -- hlog_le : -log2 μ ≤ S + nδ, with log2 μ · Real.log 2 = Real.log μ.
      -- Multiply through by Real.log 2 > 0 and use the identity.
      have hid : log2 μ * Real.log 2 = Real.log μ := by
        unfold log2; field_simp
      nlinarith [hlog_le, hl2_pos, hid,
        mul_le_mul_of_nonneg_right hlog_le hl2_pos.le]
    -- μ · 2^{S + nδ} ≥ 1  ⟺  Real.log(μ · 2^{S+nδ}) ≥ 0.
    have hlog_prod : 0 ≤ Real.log (μ * Real.rpow 2 (S + (n : ℝ) * δ)) := by
      rw [Real.log_mul hμ_pos.ne' hbase_pos.ne']
      have : Real.log (Real.rpow 2 (S + (n : ℝ) * δ)) =
          (S + (n : ℝ) * δ) * Real.log 2 :=
        Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
      rw [this]
      linarith
    exact (Real.log_nonneg_iff (mul_pos hμ_pos hbase_pos)).mp hlog_prod
  -- The count is Σ_{accepted} 1; bound each accepted 1 by μ · 2^{ΣS+nδ},
  -- and each rejected term (which is 0) trivially.
  unfold conditionallyTypicalSubspaceDimension
  calc (∑ i : TensorPower a n,
        if conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
        then (1 : ℝ) else 0)
      ≤ ∑ i : TensorPower a n,
          τ.pos.isHermitian.eigenvalues i * Real.rpow 2 (S + (n : ℝ) * δ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi :
          conditionallyTypicalEigenvalue states δ (τ.pos.isHermitian.eigenvalues i)
        · rw [if_pos hi]; exact hkey i hi
        · rw [if_neg hi]
          exact mul_nonneg (τ.pos.eigenvalues_nonneg i) hbase_pos.le
    _ = Real.rpow 2 (S + (n : ℝ) * δ) *
          ∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i := by
          rw [show (∑ i : TensorPower a n, τ.pos.isHermitian.eigenvalues i *
                Real.rpow 2 (S + (n : ℝ) * δ)) =
                ∑ i : TensorPower a n,
                  Real.rpow 2 (S + (n : ℝ) * δ) *
                    τ.pos.isHermitian.eigenvalues i from
            Finset.sum_congr rfl fun i _ => mul_comm _ _,
            Finset.mul_sum]
    _ = Real.rpow 2 (S + (n : ℝ) * δ) * 1 := by rw [hsum]
    _ = Real.rpow 2 (S + (n : ℝ) * δ) := by ring

/-! ## pack-3 HSW form

This form connects the per-symbol entropy sum `Σ_i S(σ^{x_i})` for a
`p_X`-typical codeword `x^n` to the ensemble's per-symbol entropy
average `Σ_x p_x S(σ^x)` (the classical-quantum conditional entropy
`H(B|X)` of the channel's output ensemble). It is stated concretely,
directly over the ensemble's `probs` and `states` fields; no
entropy-additivity or conditional-entropy identity is taken as a
hypothesis. The identity `H(B|X) = Σ_x p_x S(σ^x)` — equivalently
`conditionalEntropy (cqState E) = Σ_x p_x S(σ^x)` — is formalized in the
entropy category and is referenced only in prose. -/

/-- A codeword `x^n : Fin n → ι` is `p_X`-typical when its per-symbol
entropy sum `Σ_i S(σ^{x_i})` differs from the ensemble entropy-rate
`n · Σ_x p_x S(σ^x)` by at most `n δ`. The center
`Σ_x p_x S(σ^x)` is the concrete per-symbol entropy average of the
ensemble's output states (the classical-quantum conditional entropy
`H(B|X)`); it is written directly over the ensemble fields rather than
as an opaque `conditionalEntropy`. This is the per-sequence
entropy-typicality condition that feeds the HSW dimension bound. -/
def CodewordIsTypical {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) (codeword : Fin n → ι) (δ : ℝ) : Prop :=
  |∑ i, (E.states (codeword i)).vonNeumann -
      (n : ℝ) * ∑ x, ↑(E.probs x) * (E.states x).vonNeumann| ≤ (n : ℝ) * δ

/-- pack-3 (HSW form): for a `p_X`-typical codeword into the ensemble's
output states, `Tr{Π_cond} ≤ 2^{n(H(B|X) + c · δ)}` with `c = 2`, where
`H(B|X) = Σ_x p_x S(σ^x)` is the ensemble's per-symbol entropy average
(equal to `conditionalEntropy (cqState E)` by the cq-conditional-entropy
identity formalized in the entropy category). The constant `c = 2` arises
as `1` (from the typicality predicate's own `n δ` slack) plus `1` (from
the codeword's per-symbol-entropy slack `n δ` versus the rate
`n · Σ_x p_x S(σ^x)`). This form is interface-free: it assumes no
entropy-additivity or conditional-entropy identity as a hypothesis. -/
theorem conditionallyTypicalSubspaceProjector_dim_le_hsw
    {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) (codeword : Fin n → ι) (δ : ℝ) (hδ : 0 < δ)
    (hTyp : CodewordIsTypical E codeword δ) :
    conditionallyTypicalSubspaceDimension (fun i => E.states (codeword i)) δ
      ≤ Real.rpow 2
        ((n : ℝ) * (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + 2 * δ)) := by
  -- Step 1: the core dimension bound at the per-symbol entropy sum.
  have hcore := conditionallyTypicalSubspaceProjector_dim_le
    (fun i => E.states (codeword i)) δ hδ
  -- Step 2: codeword typicality bounds the per-symbol entropy sum.
  -- hTyp_ge : ∑ i S(σ^{x_i}) - n·Σ_x p_x S(σ^x) ≤ n δ,
  -- so ∑ i S(σ^{x_i}) ≤ n·Σ_x p_x S(σ^x) + n δ.
  obtain ⟨_hTyp_le, hTyp_ge⟩ := abs_le.mp hTyp
  -- Combine: Σ S(σ^{x_i}) + nδ ≤ n·Σ_x p_x S(σ^x) + nδ + nδ
  --        = n·(Σ_x p_x S(σ^x) + 2δ).
  have hsum_bound : ∑ i, (E.states (codeword i)).vonNeumann + (n : ℝ) * δ
      ≤ (n : ℝ) * (∑ x, ↑(E.probs x) * (E.states x).vonNeumann + 2 * δ) := by
    linarith
  -- Exponentiate: 2^{ΣS + nδ} ≤ 2^{n·(Σ_x p_x S(σ^x) + 2δ)}.
  refine le_trans hcore ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hsum_bound

/-! ## pack-4: projected average-state upper bound

Each accepted eigenvalue `μ` of `σ̄^{⊗ n}` satisfies the typicality predicate,
whose centered-log upper half gives the eigenvalue upper bound
`μ ≤ 2^{-n(S(σ̄) − δ)}` (the `typicalEigenvalue_le_eigenvalueUpperBound`
consequence, proved in `Typicality.lean`). In the eigenbasis of `σ̄^{⊗ n}`,
the typical projector `Π` is the `0/1` diagonal mask selecting the accepted
directions, so `Π · σ̄^{⊗ n} · Π` is the diagonal matrix carrying `μ_i` on
accepted directions and `0` elsewhere. Comparing entrywise against
`2^{-n(S(σ̄) − δ)} · Π` (which carries the scalar on accepted directions and
`0` elsewhere) gives the Loewner inequality
`Π · σ̄^{⊗ n} · Π ≤ 2^{-n(S(σ̄) − δ)} · Π`.

This is the packing-lemma `Π σ Π ≤ (1/D) Π` condition with
`D = 2^{n(S(σ̄) − δ)}`, stated for the HSW output ensemble's average state
`σ̄ = E.averageState` directly over `σ̄^{⊗ n}`. Wilde's HSW form additionally
carries a `[1 − ε]^{-1}` prefactor coming from the pruned-distribution
reduction `𝔼[σ^{X'^n}] ≤ [1 − ε]^{-1} σ̄^{⊗ n}`; that reduction is a
separate step and is not folded in here, so this is the concrete `σ̄^{⊗ n}`
form of pack-4. The proof is interface-free: it derives the eigenvalue upper
bound from the `typicalEigenvalue` predicate (no equipartition hypothesis) and
diagonalizes via the spectral theorem, the same unitary-conjugation pattern
used by `spectralPredicateProjector_le_one`. -/

/-- pack-4: the projected average state is bounded above by the scalar
`2^{-n(S(σ̄) − δ)}` times the typical projector, with
`σ̄ = E.averageState`. Concretely, for the ensemble's average state's
`n`-fold tensor power and its typical subspace projector,
`Π · σ̄^{⊗ n} · Π ≤ 2^{-n(S(σ̄) − δ)} · Π` (the packing-lemma
`Π σ Π ≤ (1/D) Π` condition with `D = 2^{n(S(σ̄) − δ)}`). The scalar is
written as a complex number so the inequality lives in the `CMatrix`
Loewner order directly. Source: [Wilde2011Qst, qit-notes.tex:28736-28747]. -/
theorem averageState_typicalProjector_projectedAvgState_le
    {n : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : Ensemble ι a) (δ : ℝ) :
    E.averageState.typicalSubspaceProjector n δ *
      (E.averageState.tensorPower n).matrix *
      E.averageState.typicalSubspaceProjector n δ
      ≤ (↑((2 : ℝ) ^ (-((n : ℝ) * E.averageState.vonNeumann - (n : ℝ) * δ))) : ℂ) •
        E.averageState.typicalSubspaceProjector n δ := by
  classical
  let σbar := E.averageState
  let τ := σbar.tensorPower n
  let hτ : τ.matrix.IsHermitian := τ.pos.isHermitian
  let U : CMatrix (TensorPower a n) := hτ.eigenvectorUnitary
  -- Eigenvalue diagonal Λ and projector mask D in the eigenbasis.
  let Λ : CMatrix (TensorPower a n) :=
    Matrix.diagonal (fun i => (hτ.eigenvalues i : ℂ))
  let D : CMatrix (TensorPower a n) :=
    Matrix.diagonal (fun i =>
      if σbar.typicalEigenvalue n δ (hτ.eigenvalues i) then (1 : ℂ) else 0)
  -- Spectral-theorem decompositions of `τ.matrix` and `Π`.
  have hspec : τ.matrix = U * Λ * star U := by
    simpa [U, Λ, Function.comp_def, Unitary.conjStarAlgAut_apply]
      using hτ.spectral_theorem
  have hU : star U * U = 1 := by
    simp [U, Unitary.coe_star_mul_self hτ.eigenvectorUnitary]
  -- The scalar `c = 2^{-n(S(σ̄) − δ)}` (real-valued, then cast to ℂ).
  set c : ℝ := 2 ^ (-((n : ℝ) * σbar.vonNeumann - (n : ℝ) * δ))
  -- Typical projector `P` (kept in `set` so the goal's projector resolves to it).
  set P : CMatrix (TensorPower a n) :=
    σbar.typicalSubspaceProjector n δ with hPi_def
  -- Unfold `P` to its `spectralPredicateProjector` form `U · D · U*`.
  have hPi : P = U * D * star U := by
    have hPi_spec : P =
      spectralPredicateProjector τ.matrix hτ
        (fun i => σbar.typicalEigenvalue n δ (hτ.eigenvalues i)) := by
      rfl
    rw [hPi_spec]
    rfl
  -- Step (i): `P · τ.matrix · P = U · (D · Λ · D) · U*`,
  -- using `star U · U = 1` twice and 0/1 idempotence of `D`.
  have hPiPiM :
      P * τ.matrix * P = U * (D * Λ * D) * star U := by
    conv_lhs => rw [hPi, hspec]
    -- Bring the adjacent `star U, U` factors together so `hU` applies, then
    -- collapse and reassociate. Use `simp only [hU]` (rather than `rw [hU]`)
    -- so the unitary-column-orthonormality fact is applied as a rewrite
    -- without the surrounding simp-normalization that pre-collapses `star U * U`.
    conv_lhs =>
      rw [show (U * D * star U) * (U * Λ * star U) =
            U * D * (star U * U) * Λ * star U by noncomm_ring]
      rw [show U * D * (star U * U) * Λ * star U * (U * D * star U) =
            U * D * (star U * U) * Λ * (star U * U) * D * star U by noncomm_ring]
      simp only [hU, one_mul, mul_one]
    noncomm_ring
  -- Step (ii): `c • P = U · (c • D) · U*`. Scalar multiplication distributes
  -- over the matrix product: `U · (c • D) = c • (U · D)`, and
  -- `(c • (U · D)) · U* = c • (U · D · U*)`.
  have hcPi : (↑c : ℂ) • P = U * ((↑c : ℂ) • D) * star U := by
    rw [hPi]
    calc (↑c : ℂ) • (U * D * star U)
          = ((↑c : ℂ) • (U * D)) * star U := by rw [← Matrix.smul_mul]
      _ = (U * ((↑c : ℂ) • D)) * star U := by rw [← Matrix.mul_smul]
      _ = U * ((↑c : ℂ) • D) * star U := rfl
  -- Step (iii): reduce the Loewner inequality to a diagonal comparison in the
  -- eigenbasis. Both sides are `U · (·) · U*`, so
  -- `(c • P) − (P · τ.matrix · P) = U · ((c • D) − (D · Λ · D)) · U*`,
  -- and the conjugation by the unitary `U` preserves positive semidefiniteness.
  rw [Matrix.le_iff]
  rw [show (↑c : ℂ) • P - P * τ.matrix * P =
        U * ((↑c : ℂ) • D - D * Λ * D) * star U by
        rw [hcPi, hPiPiM]; noncomm_ring]
  rw [Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe : IsUnit (hτ.eigenvectorUnitary : CMatrix (TensorPower a n)))]
  -- Step (iv): the inner matrix is diagonal; reduce to its diagonal entries.
  have hdiag_inner :
      ((↑c : ℂ) • D - D * Λ * D : CMatrix (TensorPower a n)) =
        Matrix.diagonal (fun i =>
          if σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
          then (↑c : ℂ) - hτ.eigenvalues i else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      -- Diagonal entry i = i.  D_ii = (if typical then 1 else 0),
      -- Λ_ii = eigenvalues_i, and (↑c • D)_ii = ↑c · D_ii.
      by_cases hi : σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
      all_goals simp [hi, D, Λ, Matrix.diagonal_apply_eq,
        Matrix.diagonal_mul_diagonal]
    · -- Off-diagonal: all three pieces are zero (every factor is diagonal).
      have hne : ∀ (f : TensorPower a n → ℂ), Matrix.diagonal f i j = 0 :=
        fun f => Matrix.diagonal_apply_ne f hij
      simp only [D, Λ, ← Matrix.diagonal_smul, Matrix.diagonal_mul_diagonal]
      -- Split the pointwise subtraction, then every `Matrix.diagonal f i j`
      -- is zero off-diagonal. Both sides reduce to `0`.
      conv_lhs => rw [show ∀ (A B : CMatrix (TensorPower a n)),
        (A - B) i j = A i j - B i j from fun _ _ => rfl]
      simp only [hne, sub_zero]
  rw [hdiag_inner]
  rw [Matrix.posSemidef_diagonal_iff]
  -- Step (v): each accepted diagonal entry `c − eigenvalues_i` is nonnegative
  -- by `typicalEigenvalue_le_eigenvalueUpperBound`; rejected entries are 0.
  intro i
  by_cases hi : σbar.typicalEigenvalue n δ (hτ.eigenvalues i)
  · simp only [hi, if_true]
    -- `eigenvalues_i ≤ c = 2^{-n(S(σ̄) − δ)}`, equivalently `0 ≤ c − eigenvalues_i`.
    have hle := σbar.typicalEigenvalue_le_eigenvalueUpperBound n δ
      (hτ.eigenvalues i) hi
    exact_mod_cast (sub_nonneg.mpr hle)
  · simp only [hi, if_false]
    exact le_refl _

end

/-! ## HSW spectral packing-hypotheses bundle

This section packages the proved spectral estimates `pack-2`, `pack-3`, `pack-4`
(own-capture, dimension, projected-average-state) into the exact 4-hypothesis
shape consumed by `PackingLemma.packingLemma_avgError`, leaving the
cross-capture hypothesis `pack-1` (`h1`) as an explicit open field.

The packing lemma operates on a generic ensemble `E : Ensemble 𝒳 sys` of output
states, a typical-subspace projector `P`, codeword projectors `Px : 𝒳 → CMatrix
sys`, and scalars `d D ε`. In the HSW direct route the system is the `n`-fold
output `sys = TensorPower b n`, the typical projector `P` is the
single-symbol-average `σ̄`-typical projector `Π(σ̄^{⊗ n}, δ)`, and the codeword
projectors `Px x` are the conditionally-typical projectors of the codeword
product states `⊗_i σ^{x_i}`. The bundle records exactly these choices and the
proved `pack-2/3/4` instantiations, so that the only remaining input to
`packingLemma_avgError` is the open cross-capture hypothesis `pack-1`
(`Re Tr(Π σ_x) ≥ 1 − ε`), discharged by a separate leaf (Task 716.3).

The spectral tolerance `ε` is a uniform scalar upper bound on the per-codeword
second-moment ratios `conditionalLogDeviationSecondMoment/(nδ)²` (the finite
spectral Chebyshev form in which `pack-2` is delivered); the constructor
requires this uniform bound as a hypothesis, so `pack-2` instantiates as
`1 − ε ≤ Re Tr(Π_x σ_x)`. The dimension bound `d` is a caller-supplied upper
bound on `Re Tr(Π_x) = conditionallyTypicalSubspaceDimension` (e.g.
`2^{n(H(B|X)+2δ)}` from `conditionallyTypicalSubspaceProjector_dim_le_hsw`). The
inverse-typical-weight `D` is `2^{n(S(σ̄) − δ)}` (from `pack-4`).
[Wilde2011Qst, qit-notes.tex:33634-33808] -/

/-- The conditionally-typical spectral weight equals the real trace of the
codeword product state against the conditionally-typical projector:
`Re Tr{(⊗_i ρ_i) · Π_cond} = conditionallyTypicalSpectralWeight`. This is the
trace-form bridge that turns `conditionallyTypicalSubspaceProjector_ownCapture`
(a bound on the spectral weight) into the packing-lemma `pack-2` trace form. It
follows from `spectralPredicateProjector_trace_mul_re` on the product state.
[Wilde2011Qst, qit-notes.tex:28704-28713] -/
theorem conditionallyTypicalSubspaceProjector_trace_mul_re {a : Type u} [Fintype a]
    [DecidableEq a] {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    ((productState states).matrix *
        conditionallyTypicalSubspaceProjector states δ).trace.re =
      conditionallyTypicalSpectralWeight states δ := by
  classical
  have hτ : (productState states).matrix.IsHermitian :=
    (productState states).pos.isHermitian
  unfold conditionallyTypicalSubspaceProjector conditionallyTypicalSpectralWeight
  exact spectralPredicateProjector_trace_mul_re _ hτ _

/-- The `pack-2` hypothesis in the trace form consumed by the packing lemma:
`Re Tr(Π_cond · (⊗_i ρ_i)) ≥ 1 − secondMoment/(nδ)²`. This is
`conditionallyTypicalSubspaceProjector_ownCapture` rewritten through the
trace-form bridge `conditionallyTypicalSubspaceProjector_trace_mul_re`, with the
projector commuted to the leading position by trace cyclicity.
[Wilde2011Qst, qit-notes.tex:28704-28713] -/
theorem conditionallyTypicalSubspaceProjector_ownCapture_trace {a : Type u} [Fintype a]
    [DecidableEq a] {n : ℕ} (states : Fin n → State a) {δ : ℝ} (hn : 0 < n)
    (hδ : 0 < δ) :
    1 - conditionalLogDeviationSecondMoment states / ((n : ℝ) * δ) ^ 2 ≤
      ((conditionallyTypicalSubspaceProjector states δ *
          (productState states).matrix).trace).re := by
  have hown := conditionallyTypicalSubspaceProjector_ownCapture states δ hn hδ
  have htr := conditionallyTypicalSubspaceProjector_trace_mul_re states δ
  have hcomm : ((conditionallyTypicalSubspaceProjector states δ *
        (productState states).matrix).trace).re =
      ((productState states).matrix *
        conditionallyTypicalSubspaceProjector states δ).trace.re :=
    congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hcomm, htr]
  exact hown

/-- The conditionally-typical-subspace dimension equals the real trace of the
conditionally-typical projector: `Re Tr(Π_cond) = conditionallyTypicalSubspaceDimension`.
This is the trace-form bridge that turns the `pack-3` dimension estimate into
the packing-lemma form `Re Tr(Π_x) ≤ d`. -/
theorem conditionallyTypicalSubspaceProjector_trace_re_eq_dimension {a : Type u}
    [Fintype a] [DecidableEq a] {n : ℕ} (states : Fin n → State a) (δ : ℝ) :
    (conditionallyTypicalSubspaceProjector states δ).trace.re =
      conditionallyTypicalSubspaceDimension states δ := by
  classical
  unfold conditionallyTypicalSubspaceProjector conditionallyTypicalSubspaceDimension
  exact spectralPredicateProjector_trace_re _ _ _

/-- **HSW spectral packing-hypotheses bundle.** For an `n`-block output
ensemble `E : Ensemble 𝒳 (TensorPower a n)` (the channel-output ensemble lifted
to `n` uses, with each `E.states x` a codeword product state `⊗_i σ^{x_i}`),
this structure bundles the typical projector `P` (the single-symbol-average
`σ̄`-typical projector `Π(σ̄^{⊗ n}, δ)`), the codeword projectors `Px` (the
conditionally-typical projectors), the scalars `d D ε`, the projector-side
hypotheses on `P` and `Px`, and the proved packing hypotheses `pack-2`/`pack-3`/
`pack-4`, in the exact shape consumed by `PackingLemma.packingLemma_avgError`.

The cross-capture hypothesis `pack-1` (`h1 : ∀ x, 1 − ε ≤ Re Tr(P · σ_x)`) is
left as an **open field with no default proof**: it is the only remaining input
that `packingLemma_avgError` requires beyond this bundle, and it is discharged
by a separate proof leaf (the unconditional-typical-subspace capture of each
codeword's product state, i.e. the pack-1 cross-capture estimate). Do not
supply a placeholder proof of `h1`; consumers must discharge it explicitly.

The fields are ordered to match `PackingLemma.packingLemma_avgError`'s argument
list (ensemble `E`, then `P`/`P`-facts, then `Px`/`Px`-facts, then
`d D ε`/sign-hypotheses, then `h1 h2 h3 h4`), so that the derandomized packing
step can feed a value of this structure straight into the packing lemma by
projection.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
structure HSWPackingHypothesesSpectral
    {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (E : Ensemble 𝒳 (TensorPower a n)) (δ : ℝ) where
  /-- The single-symbol-average typical projector `Π = Π(σ̄^{⊗ n}, δ)`. -/
  P : CMatrix (TensorPower a n)
  /-- The codeword conditionally-typical projectors `Π_x`. -/
  Px : 𝒳 → CMatrix (TensorPower a n)
  /-- Dimension bound `d` (an upper bound on `Re Tr(Π_x)`). -/
  d : ℝ
  /-- Inverse typical weight `D = 2^{n(S(σ̄) − δ)}` (strictly positive). -/
  D : ℝ
  /-- Spectral tolerance `ε ≥ 0`, a uniform upper bound on the per-codeword
  second-moment ratios `conditionalLogDeviationSecondMoment/(nδ)²`. -/
  ε : ℝ
  /-- Nonnegativity of the spectral tolerance. -/
  hε_nonneg : 0 ≤ ε
  /-- Strict positivity of the inverse typical weight `D`. -/
  hD_pos : 0 < D
  /-- The typical projector `P` is positive semidefinite. -/
  P_posSemidef : P.PosSemidef
  /-- The typical projector `P` is idempotent. -/
  P_idempotent : P * P = P
  /-- The typical projector `P` is bounded by the identity effect. -/
  P_le_one : P ≤ 1
  /-- Each codeword projector `Px x` is positive semidefinite, idempotent, and
  bounded by the identity effect (the projector-side hypothesis bundle required
  by `packingLemma_avgError`). -/
  Px_projector : ∀ x, (Px x).PosSemidef ∧ Px x * Px x = Px x ∧ Px x ≤ 1
  /-- **pack-1 (OPEN).** Cross-capture: the typical projector captures each
  codeword product state, `Re Tr(P · σ_x) ≥ 1 − ε`. This field has no default
  proof; it is the remaining input discharged separately by the
  unconditional-typical-subspace capture leaf (Task 716.3). -/
  h1 : ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re
  /-- **pack-2.** Own-capture: each codeword's conditionally-typical projector
  captures its own product state, `Re Tr(Π_x · σ_x) ≥ 1 − ε`. -/
  h2 : ∀ x, 1 - ε ≤ ((Px x * (E.states x).matrix).trace).re
  /-- **pack-3.** Dimension: the codeword-projector trace is bounded by `d`. -/
  h3 : ∀ x, ((Px x).trace).re ≤ d
  /-- **pack-4.** Projected average state: `Π · σ̄ · Π ≤ D⁻¹ · Π`, where
  `σ̄ = E.averageState` is the ensemble's `n`-block average state. -/
  h4 : P * E.averageState.matrix * P ≤ ((D : ℝ)⁻¹) • P

namespace HSWPackingHypothesesSpectral

variable {a : Type u} {𝒳 : Type*} {n : ℕ}
  [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
variable {E : Ensemble 𝒳 (TensorPower a n)} {δ : ℝ}

/-! ### pack-1 cross-capture estimates

The full per-codeword cross-capture of Wilde's conditional-typical-subspace
analysis (`prop-qt:cond-state-with-uncond-proj`: a codeword product state
`⊗_i σ^{x_i}` captured by the AVERAGE state's typical projector
`Π(σ̄^{⊗ n}, δ)`) is genuinely hard: the codeword product state is not diagonal
in the average state's eigenbasis, so the clean spectral argument used in
`pack-2` (own-capture) does not transfer. This task does not prove that.

Three small, cleanly-provable pieces are delivered here:

* **Piece A** — the AVERAGE state captures itself under its own typical
  projector (the iid self-capture; the codeword product state coincides with
  `σ̄^{⊗ n}`, which IS diagonal in its own eigenbasis, so the spectral argument
  applies). This is the same route as `pack-2`'s `ownCapture_trace` but routed
  through Task 4's high-probability form rather than the per-codeword
  second-moment bound.
* **Discharge helper** — the open `h1` field is recovered pointwise from a
  hypothesis that bounds the *deficit* `1 − Re Tr(Π σ_x)` by `ε` (mechanical
  rearrangement, no content).
* **Placeholder kernel** — the per-codeword unconditional-capture statement is
  recorded as a proof-pending `Prop`, so that the hard estimate can be tracked
  without a placeholder proof.

[Wilde2011Qst, qit-notes.tex:33634-33808] -/

/-- **Piece A.** The average state captures itself under its own typical
projector in the high-probability regime: for `σ̄ = E₀.averageState` and `n`
past the threshold `C / (ε δ²)` (with `C = typicalLogDeviationSecondMoment σ̄ 1`,
the same threshold form as Task 4's high-probability theorem),
`Re Tr(Π · σ̄^{⊗ n}) ≥ 1 − ε`. The codeword product state coincides with
`σ̄^{⊗ n}`, which is diagonal in its own eigenbasis, so the spectral argument
applies; this is the iid self-capture, NOT the per-codeword cross-capture.

Route: `Re Tr(Π · σ̄^{⊗ n})` equals `typicalSubspaceSpectralWeight σ̄ n δ` by
`typicalSubspaceProjector_trace_mul_re` (with the projector commuted to the
leading position by trace cyclicity), then apply Task 4's
`typicalSubspaceSpectralWeight_high_probability`. Source:
[Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem reTrace_averageStateTypicalProjector_self {a : Type u} [Fintype a]
    [DecidableEq a] {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a) {n : ℕ} {δ ε : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hε : 0 < ε)
    (hthresh :
      (E₀.averageState.typicalLogDeviationSecondMoment 1 / (ε * δ ^ 2)) ≤ n) :
    1 - ε ≤
      ((E₀.averageState.typicalSubspaceProjector n δ *
          (E₀.averageState.tensorPower n).matrix).trace).re := by
  -- Trace cyclicity commutes the leading projector to the trailing position,
  -- matching `typicalSubspaceProjector_trace_mul_re`'s `(τ.matrix * P)` form.
  have hcomm :
      ((E₀.averageState.typicalSubspaceProjector n δ *
          (E₀.averageState.tensorPower n).matrix).trace).re =
        (((E₀.averageState.tensorPower n).matrix *
            E₀.averageState.typicalSubspaceProjector n δ).trace).re :=
    congrArg Complex.re (Matrix.trace_mul_comm _ _)
  rw [hcomm,
    E₀.averageState.typicalSubspaceProjector_trace_mul_re n δ]
  exact E₀.averageState.typicalSubspaceSpectralWeight_high_probability
    hn hδ hε hthresh

/-- **Discharge helper.** Recover the open `h1` field pointwise from a hypothesis
bounding the *deficit* `1 − Re Tr(Π σ_x)` by `ε`. This is a mechanical
rearrangement: `1 − Re Tr(Π σ_x) ≤ ε` iff `1 − ε ≤ Re Tr(Π σ_x)` over the reals.
It does not prove cross-capture; it just re-presents an atypical-deficit bound
in the `h1` shape consumed by the packing lemma. -/
abbrev h1_of_perCodewordAtypical
    {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (_E₀ : Ensemble 𝒳 a) -- unused at this signature level; kept for symmetry
        -- with the constructor's single-symbol-ensemble framing
    (E : Ensemble 𝒳 (TensorPower a n)) (P : CMatrix (TensorPower a n))
    (ε : ℝ)
    (hatypical : ∀ x,
      1 - ((P * (E.states x).matrix).trace).re ≤ ε) :
    ∀ x, 1 - ε ≤ ((P * (E.states x).matrix).trace).re := fun x =>
  by linarith [hatypical x]

/-- **Placeholder kernel (proof-pending).** The per-codeword UNCONDITIONAL
typical-subspace capture statement — the codeword product state `⊗_i σ^{x_i}`
captured by the AVERAGE state's typical projector `Π(σ̄^{⊗ n}, δ)`:
`Re Tr(Π · σ_x) ≥ 1 − ε` for every codeword `x`.

This is the genuine HSW pack-1 cross-capture (`prop-qt:cond-state-with-uncond-proj`
in Wilde's notes). It is recorded here as a `Prop` WITHOUT a proof: the codeword
product state is not diagonal in the average state's eigenbasis, so the clean
spectral argument that delivers `pack-2` (own-capture) and Piece A above does
NOT apply. A future typicality / Markov-route leaf is expected to discharge it.
Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/
def pack1_crossCapture_unconditional_statement {a : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype 𝒳] [DecidableEq 𝒳]
    (E₀ : Ensemble 𝒳 a) (E : Ensemble 𝒳 (TensorPower a n)) (δ ε : ℝ) : Prop :=
  ∀ x, 1 - ε ≤
    ((E₀.averageState.typicalSubspaceProjector n δ * (E.states x).matrix).trace).re

/-- The codeword-product-state family `fun i => σ^{(codeword i)}` built from a
length-`n` symbol sequence into an abstract per-symbol state family. This is the
per-codeword product state whose conditionally-typical projector is `Px x`.

In the HSW channel-output setup, `symStates j = N.applyState (inputState j)`
for the channel `N` and the chosen input distribution's per-symbol states. -/
abbrev codewordStates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (symStates : ι → State a) (codeword : Fin n → ι) :
    Fin n → State a := fun i => symStates (codeword i)

end HSWPackingHypothesesSpectral

/-! ### Constructor: proved fields from the spectral estimates

The constructor `hswPackingHypothesesSpectral_of_estimates` builds the proved
fields (`P`, `Px`, `d`, `D`, `ε`, the projector facts, and
`pack-2`/`pack-3`/`pack-4`) directly from the spectral estimates in this
module, leaving `pack-1` (`h1`) as the sole open input.

The constructor is stated over a **single-symbol** ensemble `E₀ : Ensemble ι a`
(the one-use channel-output ensemble), whose average state is
`σ̄ = E₀.averageState`. The `n`-block ensemble `E : Ensemble 𝒳 (TensorPower a n)`
is required to have codeword-product states (`hstates`) and average state
`σ̄.tensorPower n` (`hσbar`), so the spectral `pack-2/3` estimates (stated for
`productState`) and the proved `pack-4` estimate
`averageState_typicalProjector_projectedAvgState_le E₀ δ` (stated for the
single-symbol average tensored to `n` copies) instantiate against `E.states x`
and `E.averageState` verbatim. -/


/-- **Constructor.** Build an `HSWPackingHypothesesSpectral` from the proved
spectral estimates, leaving `pack-1` (`h1`) as the sole open input.

The instantiated objects are:
* `P = E₀.averageState.typicalSubspaceProjector n δ` (the `σ̄^{⊗ n}` typical
  projector, with its PSD/idempotent/`≤ 1` facts from `Typicality.lean`);
* `Px x = conditionallyTypicalSubspaceProjector (codewordStates symStates (codewordOf x)) δ`
  (the codeword conditionally-typical projectors, with their projector facts);
* `D = 2^{n(S(σ̄) − δ)}` (the inverse typical weight, from `pack-4`);
* `d` and `ε` supplied by the caller (`d` a `pack-3` upper bound on the
  conditionally-typical-subspace dimension; `ε` a nonnegative uniform upper
  bound on the per-codeword second-moment ratios `secondMoment/(nδ)²`).

The hypothesis `hstates` identifies each `n`-block ensemble state matrix with
its codeword product-state matrix, so the spectral `pack-2/3` estimates
instantiate against `E.states x`. The hypothesis `hσbar` identifies the
`n`-block ensemble's average state with `σ̄.tensorPower n`, so the proved
`pack-4` estimate `averageState_typicalProjector_projectedAvgState_le E₀ δ`
instantiates against `E.averageState`. The `h1` argument is the open
cross-capture hypothesis, passed through unchanged.
[Wilde2011Qst, qit-notes.tex:33634-33808] -/
@[expose]
noncomputable def hswPackingHypothesesSpectral_of_estimates
    {a : Type u} {ι : Type u} {𝒳 : Type*} {n : ℕ}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    [Fintype 𝒳] [DecidableEq 𝒳]
    (E₀ : Ensemble ι a) (E : Ensemble 𝒳 (TensorPower a n)) (δ : ℝ)
    (symStates : ι → State a) (codewordOf : 𝒳 → Fin n → ι)
    (hn : 0 < n) (hδ : 0 < δ)
    (d ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hstates : ∀ x, (E.states x).matrix =
      (productState <|
        HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)).matrix)
    (hε_bound : ∀ x,
      conditionalLogDeviationSecondMoment
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) /
        ((n : ℝ) * δ) ^ 2 ≤ ε)
    (hpack3 : ∀ x, conditionallyTypicalSubspaceDimension
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ ≤ d)
    (hσbar : E.averageState = E₀.averageState.tensorPower n)
    (h1 : ∀ x, 1 - ε ≤
        ((E₀.averageState.typicalSubspaceProjector n δ * (E.states x).matrix).trace).re) :
    HSWPackingHypothesesSpectral E δ where
  P := E₀.averageState.typicalSubspaceProjector n δ
  Px := fun x => conditionallyTypicalSubspaceProjector
    (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ
  d := d
  D := (2 : ℝ) ^ ((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ)
  ε := ε
  hε_nonneg := hε_nonneg
  hD_pos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  P_posSemidef := E₀.averageState.typicalSubspaceProjector_posSemidef n δ
  P_idempotent := E₀.averageState.typicalSubspaceProjector_idempotent n δ
  P_le_one := E₀.averageState.typicalSubspaceProjector_le_one n δ
  Px_projector := fun x =>
    ⟨conditionallyTypicalSubspaceProjector_posSemidef
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ,
      conditionallyTypicalSubspaceProjector_idempotent
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ,
      conditionallyTypicalSubspaceProjector_le_one
        (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ⟩
  h1 := h1
  h2 := fun x => by
    -- Identify the ensemble state matrix with the codeword product-state matrix.
    rw [hstates x]
    -- Spectral `pack-2` trace form: `1 − sm_x/(nδ)² ≤ Re Tr(Π_x · ⊗ρ_i)`.
    have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
      (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) hn hδ
    -- `hε_bound` gives `sm_x/(nδ)² ≤ ε`, hence `1 − ε ≤ 1 − sm_x/(nδ)²`.
    have hkey : 1 - ε ≤
        1 - conditionalLogDeviationSecondMoment
          (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) /
          ((n : ℝ) * δ) ^ 2 := by linarith [hε_bound x]
    exact le_trans hkey hown
  h3 := fun x => by
    -- `Re Tr(Π_x) = conditionallyTypicalSubspaceDimension` (trace-counts bridge).
    rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension
      (HSWPackingHypothesesSpectral.codewordStates symStates (codewordOf x)) δ]
    exact hpack3 x
  h4 := by
    -- Proved `pack-4` for the single-symbol ensemble `E₀`: in the eigenbasis
    -- of `σ̄^{⊗ n}`, `Π · σ̄^{⊗ n} · Π ≤ ↑(2^{−n(S(σ̄)−δ)}) · Π`.
    have hpack4 := averageState_typicalProjector_projectedAvgState_le (n := n) E₀ δ
    -- Align the average-state matrix via `hσbar`: `E.averageState.matrix`
    -- equals `(σ̄.tensorPower n).matrix`, the middle factor in `hpack4`.
    rw [show E.averageState.matrix = (E₀.averageState.tensorPower n).matrix from by
        rw [hσbar]]
    -- Align the goal's real scalar `(2^{a})⁻¹` (`a = n(S(σ̄)−δ)`) to `2^{−a}`
    -- via `Real.rpow_neg` (`b^{-x} = (b^x)⁻¹`), matching `hpack4`'s real base
    -- `2^{−a}` before its `ℝ → ℂ` coercion.
    rw [show ((2 : ℝ) ^ ((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ))⁻¹ =
        (2 : ℝ) ^ (-((n : ℝ) * E₀.averageState.vonNeumann - (n : ℝ) * δ)) by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]]
    -- The goal's real-smul `(2^{−a} : ℝ) • P` and `hpack4`'s complex-smul
    -- `↑(2^{−a}) • P` agree elementwise via the `ℝ → ℂ` smul coercion.
    exact_mod_cast hpack4

/-! ## pack-4 pruned-distribution `(1 − ε)⁻¹` prefactor

Wilde's HSW form of `pack-4` carries a `[1 − ε]⁻¹` prefactor coming from the
pruned-distribution reduction. Codewords are drawn from the law `p'` obtained by
restricting the i.i.d. law `p^{⊗ n}` to the typical set (atypical mass `≤ ε`)
and renormalizing; then `p'(x^n) ≤ p^{⊗ n}(x^n) / (1 − ε)` pointwise, and
because each codeword output `σ^{x^n}` is positive semidefinite the Loewner
order of the weighted sums inherits the coefficient domination:

`𝔼_{p'}[σ^{X'^n}] = Σ_{x^n} p'(x^n) σ^{x^n} ≤ (1 − ε)⁻¹ Σ_{x^n} p^{⊗ n}(x^n) σ^{x^n}
                  = (1 − ε)⁻¹ σ̄^{⊗ n}`.

This section delivers the cleanly-provable kernel of that reduction — a
Loewner-order coefficient-domination lemma for two ensembles sharing their state
family — and records the full n-block pruned-output statement as a proof-pending
`Prop` (the missing piece is the n-block product-probability / typical-set
restriction / renormalization infrastructure, which is not present in the
repository). Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/

/-- **Coefficient-domination kernel (proved).** If two ensembles `E E'` over the
same index type share their state family and `E'`'s weights are pointwise
dominated by a nonnegative real multiple of `E`'s weights —
`(E'.probs x : ℝ) ≤ c * (E.probs x : ℝ)` for every `x`, for some `0 ≤ c` — then
the average states satisfy the Loewner inequality
`E'.averageState.matrix ≤ c • E.averageState.matrix` (the scalar `c` acting on
the complex matrix through the `ℝ → ℂ` algebra map).

Route: write `c • E.averageState.matrix − E'.averageState.matrix` as the single
sum `Σ_x (c * (E.probs x : ℝ) − (E'.probs x : ℝ)) • (E.states x).matrix` (the two
`averageState_matrix` sums coincide entry-by-entry after distributing the outer
real scalar, using ring-subtraction of the real-valued coefficients). Each
summand is positive semidefinite because the real coefficient
`c * (E.probs x) − (E'.probs x)` is nonnegative (pointwise domination) and
`(E.states x).matrix` is a density matrix; `Matrix.posSemidef_sum` lifts the
pointwise PSD fact to the sum, and `Matrix.le_iff` converts PSD-of-the-difference
back to the Loewner order. This is the kernel of the pruned-distribution
`(1 − ε)⁻¹` prefactor for `pack-4`; the full HSW instantiation is the
proof-pending `pack4_prunedReduction_statement` below. -/
theorem averageState_le_of_probDomination {a : Type u} {ι : Type u}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (E E' : Ensemble ι a) {c : ℝ} (hc : 0 ≤ c)
    (hstates : ∀ x, E.states x = E'.states x)
    (hdom : ∀ x, (E'.probs x : ℝ) ≤ c * (E.probs x : ℝ)) :
    E'.averageState.matrix ≤ c • E.averageState.matrix := by
  -- Unfold both Loewner order and `averageState` into the PSD-of-difference form.
  rw [Matrix.le_iff]
  -- Symmetrize the state families: rewrite `E'.states` as `E.states` throughout.
  have hstates' : ∀ x, E'.states x = E.states x := fun x => (hstates x).symm
  -- Express the difference as a single sum of per-index PSD summands. The real
  -- scalar distributes over the `averageState_matrix` sum; ring-subtraction of
  -- the real coefficients then factors each summand as a single real smul.
  have hkey : (c • E.averageState.matrix : CMatrix a) - E'.averageState.matrix =
      ∑ x, ((c * (E.probs x : ℝ) - (E'.probs x : ℝ)) : ℝ) • (E.states x).matrix := by
    ext i j
    simp only [Ensemble.averageState_matrix, Matrix.sub_apply, Finset.smul_sum,
      Matrix.smul_apply, Matrix.sum_apply]
    -- Rewrite both the outer `ℝ` smul and the per-index `ℝ≥0` smul to the
    -- common `algebraMap … * _` form, then normalize every algebraMap to the
    -- `ℝ≥0 → ℝ → ℂ` coercion so `push_cast` + `ring` can close over `ℂ`.
    simp only [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
      NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    have hseq : ∀ x, (E'.states x).matrix i j = (E.states x).matrix i j :=
      fun x => by rw [hstates']
    simp only [hseq]
    -- Combine the two LHS sums into a single sum via `sum_sub_distrib`, then
    -- close per-index by `ring` (the only structural difference is the
    -- scalar/matrix-entry multiplication order, which `ring` reorders).
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring
  rw [hkey]
  -- Each summand `(c * E.probs x − E'.probs x) • (E.states x).matrix` is PSD:
  -- the real coefficient is nonnegative — `hc` makes `c * ↑p ≥ 0`, and `hdom`
  -- gives `↑p' ≤ c * ↑p`, so `0 ≤ c * ↑p − ↑p'` — and the density matrix
  -- `(E.states x).matrix` is PSD; `PosSemidef.smul` lifts.
  refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
  have hp_nonneg : 0 ≤ (E.probs x : ℝ) := NNReal.coe_nonneg _
  have hcoeff_nonneg : 0 ≤ c * (E.probs x : ℝ) - (E'.probs x : ℝ) := by
    have : 0 ≤ c * (E.probs x : ℝ) := mul_nonneg hc hp_nonneg
    linarith [hdom x, this]
  exact (E.states x).pos.smul hcoeff_nonneg

/-- **n-block product-of-expectations identity.** The expectation of the
codeword product state under the i.i.d. product law equals the tensor power
of the average state:

`Σ_{x : Fin n → ι} (∏ i, probs (x i)) • (⊗_i σ^{x_i}).matrix = σ̄^{⊗ n}.matrix`

where `σ̄` has matrix `Σ_j (probs j) • (symStates j).matrix`. This is the
crux of the pruned-distribution reduction: the i.i.d. law's expected codeword
output is exactly the tensor power of the per-symbol average, so any
Loewner-order bound on `σ̄^{⊗ n}` transfers to the expected pruned output.

The proof inducts on `n` at the matrix-entry level. In the successor step
the sum over `Fin (n + 1) → ι` is split head/tail via `Fin.consEquiv`, the
probability product splits via `Fin.prod_univ_succ`, the head sum collapses
to `σ̄.matrix` by hypothesis, and the tail sum is the induction hypothesis. -/
theorem averageState_eq_tensorPower_of_iid {a ι : Type*} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι] (symStates : ι → State a) (probs : ι → ℝ≥0)
    (σbar : State a) (hσbar : σbar.matrix = ∑ j, (probs j) • (symStates j).matrix) :
    ∀ (n : ℕ) (X Y : TensorPower a n),
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) X Y =
        (σbar.tensorPower n).matrix X Y
  | 0, X, Y => by
    -- n = 0: there is a unique empty codeword, the empty probability product
    -- is 1, and `productState` / `σbar.tensorPower 0` are both `State.unit`.
    let e : Fin 0 → ι := fun i => i.elim0
    have hsub : ∀ x : Fin 0 → ι, x = e := fun x => by funext i; exact i.elim0
    have huniv : (Finset.univ : Finset (Fin 0 → ι)) = {e} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton]
      exact ⟨fun _ => hsub x, fun hx => trivial⟩
    -- The sum over the singleton index set equals its single summand.
    rw [huniv, Finset.sum_singleton]
    -- Empty probability product is 1 (`Fin.prod_univ_zero`).
    rw [Fin.prod_univ_zero, one_smul, productState_zero, State.tensorPower_zero]
  | n + 1, (X0, Xs), (Y0, Ys) => by
    -- n + 1: unfold both sides into head/tail Kronecker factors. The codeword
    -- sum is transported through the head/tail bijection
    -- `ι × (Fin n → ι) ≃ Fin (n+1) → ι` (`Fin.cons`); after splitting the
    -- probability product and the Kronecker entry, the double sum factors via
    -- `Fintype.sum_mul_sum` into `(σbar.matrix X0 Y0) * ((σbar.tensorPower n).matrix Xs Ys)`,
    -- matching the RHS Kronecker expansion.
    -- Define the head/tail entry functions we will sum.
    let head : ι → ℂ := fun x0 => (probs x0 : ℂ) * (symStates x0).matrix X0 Y0
    let tail : (Fin n → ι) → ℂ := fun xs =>
      (∏ i, probs (xs i)) • (productState (fun i => symStates (xs i))).matrix Xs Ys
    -- Pointwise summand identity: under `Fin.cons`, the codeword summand at
    -- entry `(X0,Xs),(Y0,Ys)` equals `head x0 * tail xs`.
    have hsummand : ∀ (x0 : ι) (xs : Fin n → ι),
        (∏ i, probs ((Fin.cons x0 xs : Fin (n + 1) → ι) i)) •
          (productState (fun i => symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) i))).matrix
            (X0, Xs) (Y0, Ys) =
        head x0 * tail xs := by
      intro x0 xs
      -- Split the probability product (head * tail).
      have hprod : ∏ i, probs ((Fin.cons x0 xs : Fin (n + 1) → ι) i) =
          probs x0 * ∏ i, probs (xs i) := by
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
      -- Unfold the productState matrix entry to its head/tail Kronecker product.
      have hentry :
          (productState fun i => symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) i)).matrix
            (X0, Xs) (Y0, Ys) =
            (symStates x0).matrix X0 Y0 *
              (productState fun i => symStates (xs i)).matrix Xs Ys := by
        -- Reduce `productState (cons head/tail)` to `(symStates head).prod (productState tail)`
        -- by `productState_succ` and `Fin.cons_zero`/`Fin.cons_succ`, then read off the
        -- matrix entry via `prod_matrix_kronecker` + `kronecker_apply`.
        have htail_eq : (fun j : Fin n =>
            symStates ((Fin.cons x0 xs : Fin (n + 1) → ι) j.succ)) =
            (fun j : Fin n => symStates (xs j)) := by
          funext j; simp only [Fin.cons_succ]
        conv_lhs => rw [productState_succ, htail_eq]
        rw [State.prod_matrix_kronecker]
        simp only [Fin.cons_zero]
        rfl
      -- Split the `ℝ≥0 → ℂ` smul across the `ℂ` product.
      rw [hprod, hentry]
      -- Coerce both scalars to `ℂ` explicitly so the only remaining algebra is
      -- commutativity of `ℂ` (no opaque `∏` of coerced elements for `ring`).
      have hkey : ((probs x0 * ∏ i, probs (xs i) : ℝ≥0) •
            ((symStates x0).matrix X0 Y0 * (productState fun i => symStates (xs i)).matrix Xs Ys : ℂ)) =
          ((probs x0 : ℂ) * (symStates x0).matrix X0 Y0) *
            ((∏ i, probs (xs i)) • (productState fun i => symStates (xs i)).matrix Xs Ys) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        -- Split the product-scalar cast without unfolding the `∏`.
        rw [show ((algebraMap ℝ≥0 ℂ) (probs x0 * ∏ i, probs (xs i))) =
              (algebraMap ℝ≥0 ℂ) (probs x0) * (algebraMap ℝ≥0 ℂ) (∏ i, probs (xs i)) from
            map_mul _ _ _]
        rw [IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ, NNReal.algebraMap_eq_coe,
          Complex.coe_algebraMap, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
          NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
        ring
      rw [hkey]
    -- The head-sum is `σbar.matrix X0 Y0` by `hσbar` (entrywise).
    have hhead_sum : ∑ x0, head x0 = σbar.matrix X0 Y0 := by
      rw [hσbar]
      simp only [Matrix.sum_apply, Matrix.smul_apply, head]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
        NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    -- The tail-sum is `(σbar.tensorPower n).matrix Xs Ys` by the IH.
    have htail_sum : ∑ xs, tail xs = (σbar.tensorPower n).matrix Xs Ys := by
      have key : (∑ xs : Fin n → ι,
          (∏ i, probs (xs i)) • (productState (fun i => symStates (xs i))).matrix) Xs Ys
          = (σbar.tensorPower n).matrix Xs Ys :=
        averageState_eq_tensorPower_of_iid symStates probs σbar hσbar n Xs Ys
      simp only [Matrix.sum_apply, Matrix.smul_apply, tail] at key ⊢
      exact key
    -- RHS: `(σbar.tensorPower (n+1)).matrix (X0,Xs) (Y0,Ys)` is the head/tail
    -- Kronecker product `σbar.matrix X0 Y0 * (σbar.tensorPower n).matrix Xs Ys`.
    rw [show (σbar.tensorPower (n + 1)).matrix (X0, Xs) (Y0, Ys) =
        σbar.matrix X0 Y0 * (σbar.tensorPower n).matrix Xs Ys from by
        rw [State.tensorPower_succ, State.prod_matrix_kronecker]
        rfl]
    -- Combine: RHS = head-sum * tail-sum.
    rw [← hhead_sum, ← htail_sum]
    -- Push the LHS entry application into the sum, factor via `sum_mul_sum`,
    -- then transport the `(x0,xs)`-product-type sum back to the codeword sum.
    rw [Matrix.sum_apply]
    rw [Fintype.sum_mul_sum head tail]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin n → ι) => head p.1 * tail p.2)]
    exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => ι))
      (fun p => head p.1 * tail p.2)
      (fun x => (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix (X0, Xs) (Y0, Ys))
      (fun p => (hsummand p.1 p.2).symm)).symm


/-- **pack-4 pruned-distribution reduction.** The HSW `(1 − ε)⁻¹` prefactor on
the expected pruned-distribution codeword output. Let `symStates : ι → State a`
be the per-symbol channel outputs, `probs : ι → ℝ≥0` the input law, and
`σbar` the per-symbol average output state with matrix
`σbar.matrix = Σ_j (probs j) • (symStates j).matrix`. If a pruned ensemble
`E_pruned : Ensemble (Fin n → ι) (TensorPower a n)` has

* codeword-product outputs `E_pruned.states x = productState (fun i => symStates (x i))`
  (same family as the i.i.d. law), and
* pruned weights pointwise dominated by `(1 − ε)⁻¹` times the i.i.d. product
  law, `(E_pruned.probs x : ℝ) ≤ (1 − ε)⁻¹ * ∏ i, (probs (x i) : ℝ)`,

then the expected pruned codeword output is Loewner-bounded by the renormalized
tensor power:

`E_pruned.averageState.matrix ≤ ((1 − ε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix`.

This is the `(1 − ε)⁻¹` renormalization step of the HSW packing argument: the
typical-set restriction discards atypical mass `≤ ε` and renormalizes the
surviving mass by `(1 − ε)⁻¹`, so the expected pruned output is dominated by the
renormalized i.i.d. average `σ̄^{⊗ n}`. The hypothesis `ε < 1` keeps the inverse
well-defined and nonneg.

Proof route: unfold `E_pruned.averageState.matrix` and `(σbar.tensorPower n).matrix`
into their per-codeword sums (the latter via `averageState_eq_tensorPower_of_iid`),
rewrite the pruned states via `hstates`, and reduce to positive-semidefiniteness
of the single difference sum
`Σ_x ((1 − ε)⁻¹ * ∏_i probs (x_i) − E_pruned.probs x) • (productState ...).matrix`,
which follows from `Matrix.posSemidef_sum` plus each coefficient nonneg
(pointwise domination `hdom`, with `ε < 1` giving `(1 − ε)⁻¹ ≥ 0`) and each
`productState.matrix` positive semidefinite. This mirrors
`averageState_le_of_probDomination` with the i.i.d. law substituted for the
dominating ensemble's weights. Source: [Wilde2011Qst, qit-notes.tex:33634-33808]. -/
theorem pack4_prunedReduction_statement {a : Type u} {ι : Type u}
    [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]
    (symStates : ι → State a) (probs : ι → ℝ≥0) (σbar : State a)
    (hσbar : σbar.matrix = ∑ j, (probs j) • (symStates j).matrix)
    {n : ℕ} {ε : ℝ} (hε : ε < 1)
    (E_pruned : Ensemble (Fin n → ι) (TensorPower a n))
    (hstates : ∀ x : Fin n → ι,
      E_pruned.states x = productState (fun i => symStates (x i)))
    (hdom : ∀ x : Fin n → ι,
      (E_pruned.probs x : ℝ) ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ)) :
    E_pruned.averageState.matrix ≤ ((1 - ε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
  -- `(1 − ε)⁻¹` is nonneg because `ε < 1` gives `0 < 1 − ε`.
  have hε_pos : 0 < 1 - ε := by linarith
  have hinv_nonneg : 0 ≤ (1 - ε)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hε_pos)
  -- Replace the RHS tensor-power matrix by the i.i.d. product sum (entrywise).
  have hiid : ∀ X Y,
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) X Y =
        (σbar.tensorPower n).matrix X Y :=
    averageState_eq_tensorPower_of_iid symStates probs σbar hσbar n
  -- Lift the entrywise identity to a matrix equality.
  have hiid_matrix :
      (∑ x : Fin n → ι,
          (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix) =
        (σbar.tensorPower n).matrix := by
    ext X Y; exact hiid X Y
  rw [Matrix.le_iff]
  -- Reduce to positive-semidefiniteness of the difference, with the RHS
  -- rewritten as the i.i.d. product sum.
  rw [← hiid_matrix]
  have hkey :
      ((1 - ε)⁻¹ •
          (∑ x : Fin n → ι,
              (∏ i, probs (x i)) • (productState (fun i => symStates (x i))).matrix)
          : CMatrix (TensorPower a n)) -
        E_pruned.averageState.matrix =
      ∑ x : Fin n → ι,
        (((1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) - (E_pruned.probs x : ℝ)) : ℝ) •
          (productState (fun i => symStates (x i))).matrix := by
    -- First rewrite the pruned average state's member states via `hstates`.
    have hpruned_sum :
        E_pruned.averageState.matrix =
          ∑ x : Fin n → ι,
            (E_pruned.probs x) • (productState (fun i => symStates (x i))).matrix := by
      rw [Ensemble.averageState_matrix]
      exact Finset.sum_congr rfl fun x _ => by rw [hstates x]
    rw [hpruned_sum]
    ext i j
    simp only [Matrix.sub_apply, Finset.smul_sum, Matrix.smul_apply, Matrix.sum_apply]
    -- Coerce both the outer `ℝ` smul and the per-codeword `ℝ≥0` smul to the
    -- common `algebraMap … * _` form, then normalize via `push_cast` + `ring`.
    simp only [Algebra.smul_def,
      IsScalarTower.algebraMap_apply ℝ≥0 ℝ ℂ,
      NNReal.algebraMap_eq_coe, Complex.coe_algebraMap]
    -- Combine the two sums into one via `sum_sub_distrib`, then close per-index.
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    ring
  rw [hkey]
  -- Each summand is PSD: the real coefficient is nonneg (`hdom` + `(1−ε)⁻¹ ≥ 0`
  -- and each `probs` coerces nonneg), and `productState.matrix` is PSD.
  refine Matrix.posSemidef_sum Finset.univ fun x _ => ?_
  have hprod_nonneg : 0 ≤ ∏ i, (probs (x i) : ℝ) := by
    apply Finset.prod_nonneg
    intro i _
    exact NNReal.coe_nonneg _
  have hcoeff_nonneg :
      0 ≤ ((1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) - (E_pruned.probs x : ℝ) : ℝ) := by
    have hlhs_nonneg : 0 ≤ (1 - ε)⁻¹ * ∏ i, (probs (x i) : ℝ) :=
      mul_nonneg hinv_nonneg hprod_nonneg
    have hpr_nonneg : 0 ≤ (E_pruned.probs x : ℝ) := NNReal.coe_nonneg _
    linarith [hdom x, hlhs_nonneg, hpr_nonneg]
  exact (productState (fun i => symStates (x i))).pos.smul hcoeff_nonneg

end QIT
