/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Information.Renyi.RenyiDPI.LowAlpha

/-!
# Conditional Renyi and measurement reductions

Conditional sandwiched Renyi duality reductions and measurement-map
monotonicity support.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

namespace State

open RenyiDPI.Statement

/-- The maximally mixed state is full-rank on a nonempty finite system. -/
theorem maximallyMixed_posDef [Nonempty a] :
    (maximallyMixed a).matrix.PosDef := by
  have hcard_pos : 0 < ((Fintype.card a : ℝ)⁻¹ : ℝ) := by
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)
  have hcard_pos_complex : (0 : ℂ) < (((Fintype.card a : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcard_pos
  rw [maximallyMixed_matrix]
  exact (IsStrictlyPositive.smul hcard_pos_complex
    (Matrix.PosDef.isStrictlyPositive (Matrix.PosDef.one : (1 : CMatrix a).PosDef))).posDef

/-- The normalized product reference `π_A ⊗ σ_B` is full-rank whenever
`σ_B` is full-rank. -/
theorem maximallyMixed_prod_posDef [Nonempty a]
    (σ : State b) (hσ : σ.matrix.PosDef) :
    ((maximallyMixed a).prod σ).matrix.PosDef :=
  State.prod_posDef (maximallyMixed_posDef (a := a)) hσ

/-- Conditional Renyi's unnormalized reference `I_A ⊗ σ_B` is the dimension
factor times the normalized product reference `π_A ⊗ σ_B`.

The state argument supplies nonemptiness of the left register without adding a
global typeclass precondition. This is the normalization bridge needed before
using the already-proved normalized sandwiched Renyi DPI in candidate-level
conditional Renyi arguments. -/
theorem conditionalRenyi_identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod
    (ρ : State (Prod a b)) (σ : State b) :
    identityTensorStateMatrix (a := a) σ =
      ((Fintype.card a : ℂ) •
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ).matrix) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa using identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod (a := a) σ

/-- Full-rank witness for the normalized product reference associated with a
conditional Renyi side-information state. -/
theorem conditionalRenyi_normalizedReference_posDef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) :
    ((@maximallyMixed a _ _ (by
      rcases ρ.nonempty with ⟨x⟩
      exact ⟨x.1⟩)).prod σ).matrix.PosDef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  simpa using maximallyMixed_prod_posDef (a := a) σ hσ

/-- Real powers of the conditional Renyi unnormalized reference split into the
dimension factor and the normalized product reference power.

This is the first matrix-level normalization step toward rewriting
conditional sandwiched Renyi candidates as `log₂ |A|` minus a normalized
sandwiched Renyi divergence. -/
theorem conditionalRenyi_identityTensorStateMatrix_rpow_eq_card_rpow_smul
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    CFC.rpow (identityTensorStateMatrix (a := a) σ) s =
      (((Fintype.card a : ℝ) ^ s : ℝ) : ℂ) •
        CFC.rpow
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ).matrix s := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := by positivity
  have href_psd :
      (((maximallyMixed a).prod σ).matrix).PosSemidef :=
    (conditionalRenyi_normalizedReference_posDef ρ σ hσ).posSemidef
  rw [conditionalRenyi_identityTensorStateMatrix_eq_card_smul_maximallyMixed_prod ρ σ]
  simpa using
    (cMatrix_rpow_real_smul_posSemidef_schatten
      (A := ((maximallyMixed a).prod σ).matrix)
      href_psd (lambda := (Fintype.card a : ℝ)) (s := s) hcard_nonneg)

/-- The conditional Renyi sandwich formed with `I_A ⊗ σ_B` is the corresponding
normalized-reference sandwich scaled by `|A|^s * |A|^s`.

This is the second algebraic normalization step for conditional candidates. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
        CFC.rpow (identityTensorStateMatrix (a := a) σ) s =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s : ℝ) •
        (CFC.rpow
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ).matrix s *
          ρ.matrix *
            CFC.rpow
              ((@maximallyMixed a _ _ (by
                rcases ρ.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod σ).matrix s)) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalRenyi_identityTensorStateMatrix_rpow_eq_card_rpow_smul ρ σ hσ s]
  simp [smul_smul, mul_assoc]

/-- The normalized product-reference sandwich used to compare conditional
Renyi candidates is positive semidefinite. -/
theorem conditionalRenyi_normalizedReference_sandwich_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    (CFC.rpow
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ).matrix s *
      ρ.matrix *
        CFC.rpow
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ).matrix s).PosSemidef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν : CMatrix (Prod a b) := ((maximallyMixed a).prod σ).matrix
  let C : CMatrix (Prod a b) := CFC.rpow ν s
  have hν : ν.PosDef := by
    simpa [ν] using conditionalRenyi_normalizedReference_posDef ρ σ hσ
  have hC : C.PosSemidef := by
    simpa [C, ν] using (cMatrix_rpow_posDef_of_posDef hν s).posSemidef
  have hCstar : star C = C := hC.isHermitian.eq
  have hinner : (star C * ρ.matrix * C).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same ρ.pos C
  rw [hCstar] at hinner
  simpa [ν, C] using hinner

/-- The unnormalized conditional-reference sandwich is positive semidefinite,
as a nonnegative scalar multiple of the normalized product-reference sandwich. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_posSemidef
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s : ℝ) :
    (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
      CFC.rpow (identityTensorStateMatrix (a := a) σ) s).PosSemidef := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul ρ σ hσ s]
  exact Matrix.PosSemidef.smul
    (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) (by positivity)

/-- The conditional-reference sandwich power trace differs from the normalized
product-reference sandwich power trace by the explicit dimension factor.

This is the trace-power version of
`conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul`. -/
theorem conditionalRenyi_identityTensorStateMatrix_sandwich_psdTracePower_eq_card_factor
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (s p : ℝ) :
    psdTracePower
        (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) s)
        (conditionalRenyi_identityTensorStateMatrix_sandwich_posSemidef ρ σ hσ s) p =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ p) *
        psdTracePower
          (CFC.rpow
              ((@maximallyMixed a _ _ (by
                rcases ρ.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod σ).matrix s *
            ρ.matrix *
              CFC.rpow
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ).matrix s)
          (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) p := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  unfold psdTracePower
  rw [conditionalRenyi_identityTensorStateMatrix_sandwich_eq_card_factor_smul ρ σ hσ s]
  rw [cMatrix_rpow_real_smul_posSemidef_schatten
    (conditionalRenyi_normalizedReference_sandwich_posSemidef ρ σ hσ s) (by positivity)]
  rw [Matrix.trace_smul]
  simp

/-- Specialization of the conditional-reference trace-power normalization to
the sandwiched Renyi exponent. The right side is the ordinary sandwiched Renyi
inner trace-power against the normalized product reference `π_A ⊗ σ_B`. -/
theorem conditionalRenyi_identityTensorStateMatrix_inner_tracePower_eq_card_factor
    (ρ : State (Prod a b)) (σ : State b) (hσ : σ.matrix.PosDef) (α : ℝ) :
    let s : ℝ := (1 - α) / (2 * α)
    (CFC.rpow
        (CFC.rpow (identityTensorStateMatrix (a := a) σ) s * ρ.matrix *
          CFC.rpow (identityTensorStateMatrix (a := a) σ) s) α).trace.re =
      (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α) *
        psdTracePower
          (sandwichedRenyiInner ρ
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ) α)
          (sandwichedRenyiInner_posSemidef ρ
            ((@maximallyMixed a _ _ (by
              rcases ρ.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ) α) α := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  intro s
  have h :=
    conditionalRenyi_identityTensorStateMatrix_sandwich_psdTracePower_eq_card_factor
      (ρ := ρ) (σ := σ) hσ s α
  simpa [psdTracePower, sandwichedRenyiInner] using h

/-- Conditional sandwiched Renyi candidates can be rewritten using the
normalized product reference `π_A ⊗ σ_B`, at the cost of an explicit dimension
factor inside the logarithm. This is the value-level handoff from the
subnormalized `I_A ⊗ σ_B` definition to the ordinary sandwiched divergence
kernel used by channel DPI. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_factor_mul_normalizedTracePower
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      (-(1 / (α - 1))) *
        log2
          ((((Fintype.card a : ℝ) ^ ((1 - α) / (2 * α)) *
                (Fintype.card a : ℝ) ^ ((1 - α) / (2 * α))) ^ α) *
            psdTracePower
              (sandwichedRenyiInner ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α)
              (sandwichedRenyiInner_posSemidef ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α) α) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  dsimp [conditionalSandwichedRenyiCandidate]
  change (-(1 / (α - 1))) *
      log2
        ((CFC.rpow
          (CFC.rpow (identityTensorStateMatrix (a := a) σ) ((1 - α) / (2 * α)) *
            ρ.matrix *
              CFC.rpow (identityTensorStateMatrix (a := a) σ) ((1 - α) / (2 * α)))
          α).trace.re) = _
  rw [conditionalRenyi_identityTensorStateMatrix_inner_tracePower_eq_card_factor ρ σ hσ α]
  rfl

omit [DecidableEq a] in
/-- The dimension factor introduced by replacing `I_A ⊗ σ_B` with
`π_A ⊗ σ_B` simplifies to `|A|^(1-α)` at the sandwiched Renyi exponent. -/
theorem conditionalRenyi_card_factor_eq_rpow_card_one_sub [Nonempty a]
    {α : ℝ} (hα : 0 < α) :
    let s : ℝ := (1 - α) / (2 * α)
    (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α) =
      (Fintype.card a : ℝ) ^ (1 - α) := by
  intro s
  have hcard : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcard_nonneg : 0 ≤ (Fintype.card a : ℝ) := le_of_lt hcard
  have hs_nonneg : 0 ≤ (Fintype.card a : ℝ) ^ s :=
    Real.rpow_nonneg hcard_nonneg s
  have hsα : (s + s) * α = 1 - α := by
    dsimp [s]
    field_simp [ne_of_gt hα]
    ring
  calc
    (((Fintype.card a : ℝ) ^ s * (Fintype.card a : ℝ) ^ s) ^ α)
        = (((Fintype.card a : ℝ) ^ (s + s)) ^ α) := by
          rw [Real.rpow_add hcard s s]
    _ = (Fintype.card a : ℝ) ^ ((s + s) * α) := by
          rw [← Real.rpow_mul hcard_nonneg (s + s) α]
    _ = (Fintype.card a : ℝ) ^ (1 - α) := by
          rw [hsα]

/-- Candidate rewrite with the dimension factor simplified to `|A|^(1-α)`. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_one_sub_mul_normalizedTracePower
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      (-(1 / (α - 1))) *
        log2
          (((Fintype.card a : ℝ) ^ (1 - α)) *
            psdTracePower
              (sandwichedRenyiInner ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α)
              (sandwichedRenyiInner_posSemidef ρ
                ((@maximallyMixed a _ _ (by
                  rcases ρ.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod σ) α) α) := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_factor_mul_normalizedTracePower
    ρ hρ σ hσ α hα_pos hα_ne_one]
  rw [conditionalRenyi_card_factor_eq_rpow_card_one_sub (a := a) hα_pos]

/-- Base-two logarithms linearize positive real powers. -/
theorem log2_rpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    log2 (x ^ y) = y * log2 x := by
  unfold log2
  rw [Real.log_rpow hx]
  ring

/-- A conditional sandwiched Renyi candidate with the unnormalized reference
`I_A ⊗ σ_B` equals `log₂ |A|` minus the ordinary sandwiched Renyi divergence
against the normalized product reference `π_A ⊗ σ_B`.

This is the value-level bridge needed to convert the low-`α` conditional
duality route back into the already proved high-`β` channel DPI. -/
theorem conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one =
      log2 (Fintype.card a : ℝ) -
        sandwichedRenyi ρ
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ)
          hρ
          (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
          α hα_pos hα_ne_one := by
  haveI : Nonempty a := by
    rcases ρ.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν : State (Prod a b) := (maximallyMixed a).prod σ
  have hν : ν.matrix.PosDef := by
    simpa [ν] using conditionalRenyi_normalizedReference_posDef ρ σ hσ
  have hTpos :
      0 <
        psdTracePower (sandwichedRenyiInner ρ ν α)
          (sandwichedRenyiInner_posSemidef ρ ν α) α :=
    sandwichedRenyiInner_psdTracePower_pos ρ ν hρ hν α
  have hcard : 0 < (Fintype.card a : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hcardpow : 0 < (Fintype.card a : ℝ) ^ (1 - α) :=
    Real.rpow_pos_of_pos hcard (1 - α)
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_one_sub_mul_normalizedTracePower
    ρ hρ σ hσ α hα_pos hα_ne_one]
  rw [sandwichedRenyi_eq_log2_psdTracePower_inner]
  rw [log2_mul (ne_of_gt hcardpow) (ne_of_gt hTpos)]
  rw [log2_rpow_pos hcard]
  field_simp [hα_ne_one]
  ring

/-- Heterogeneous candidate comparison after normalizing the conditional
reference. This packages the value bridge in an inequality-oriented form:
to compare conditional candidates, it suffices to compare the corresponding
`log₂ dim - D̃_α(· ‖ π ⊗ σ)` quantities. -/
theorem conditionalSandwichedRenyiCandidate_le_of_normalizedReference_bound
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (hρ₁ : ρ₁.matrix.PosDef)
    (σ₁ : State b₁) (hσ₁ : σ₁.matrix.PosDef)
    (ρ₂ : State (Prod a₂ b₂)) (hρ₂ : ρ₂.matrix.PosDef)
    (σ₂ : State b₂) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hbound :
      log2 (Fintype.card a₂ : ℝ) -
          sandwichedRenyi ρ₂
            ((@maximallyMixed a₂ _ _ (by
              rcases ρ₂.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ₂)
            hρ₂
            (conditionalRenyi_normalizedReference_posDef ρ₂ σ₂ hσ₂)
            α hα_pos hα_ne_one ≤
        log2 (Fintype.card a₁ : ℝ) -
          sandwichedRenyi ρ₁
            ((@maximallyMixed a₁ _ _ (by
              rcases ρ₁.nonempty with ⟨x⟩
              exact ⟨x.1⟩)).prod σ₁)
            hρ₁
            (conditionalRenyi_normalizedReference_posDef ρ₁ σ₁ hσ₁)
            α hα_pos hα_ne_one) :
    ρ₂.conditionalSandwichedRenyiCandidate hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one ≤
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one := by
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₂ hρ₂ σ₂ hσ₂ α hα_pos hα_ne_one]
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₁ hρ₁ σ₁ hσ₁ α hα_pos hα_ne_one]
  exact hbound

/-- A normalized-reference nonnegativity bound gives the standard dimensional
upper bound on each upward conditional Renyi candidate.

This is the value-level form of the source proof obligation: after rewriting
`H̃^↑_α(A|B)` candidates as `log₂ |A| - D̃_α(ρ_AB ‖ π_A ⊗ σ_B)`, ordinary
nonnegativity of the sandwiched Renyi divergence gives
`candidate ≤ log₂ |A|`. -/
theorem conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_pos : 0 < α) (hα_ne_one : α ≠ 1)
    (hnonneg :
      0 ≤ sandwichedRenyi ρ
        ((@maximallyMixed a _ _ (by
          rcases ρ.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ)
        hρ
        (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
        α hα_pos hα_ne_one) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α hα_pos hα_ne_one ≤
      log2 (Fintype.card a : ℝ) := by
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ hρ σ hσ α hα_pos hα_ne_one]
  linarith

/-- A pointwise normalized-reference nonnegativity theorem bounds the whole
upward conditional Renyi candidate set by `log₂ |A|`.

This packages the remaining high-parameter minimax boundedness side condition
into the mathematically standard nonnegativity obligation for ordinary
sandwiched Renyi divergence. -/
theorem conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_normalizedReference_nonneg
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα : 1 / 2 ≤ α) (hα_ne_one : α ≠ 1)
    (hnonneg :
      ∀ σ : State b, ∀ hσ : σ.matrix.PosDef,
        0 ≤ sandwichedRenyi ρ
          ((@maximallyMixed a _ _ (by
            rcases ρ.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ)
          hρ
          (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
          α (by linarith) hα_ne_one) :
    BddAbove (ρ.conditionalSandwichedRenyiValueSet hρ α hα hα_ne_one) :=
  conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    ρ hρ α hα hα_ne_one
    (fun σ hσ =>
      conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
        ρ hρ σ hσ α (by linarith) hα_ne_one (hnonneg σ hσ))

/-- In the already-proved `α > 1` range, every upward conditional Renyi
candidate is bounded above by `log₂ |A|`.

This discharges the normalized-reference nonnegativity side condition using
the terminal-channel proof of ordinary sandwiched Renyi nonnegativity. -/
theorem conditionalSandwichedRenyiCandidate_le_log2_card_of_one_lt
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (σ : State b) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    ρ.conditionalSandwichedRenyiCandidate hρ σ hσ α
        (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one) ≤
      log2 (Fintype.card a : ℝ) :=
  conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
    ρ hρ σ hσ α (lt_trans zero_lt_one hα_gt_one) (ne_of_gt hα_gt_one)
    (sandwichedRenyi_nonneg_of_one_lt
      ρ
      ((@maximallyMixed a _ _ (by
        rcases ρ.nonempty with ⟨x⟩
        exact ⟨x.1⟩)).prod σ)
      hρ
      (conditionalRenyi_normalizedReference_posDef ρ σ hσ)
      α hα_gt_one)

/-- The upward conditional Renyi candidate set is bounded above by
`log₂ |A|` in the already-proved `α > 1` range. -/
theorem conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_one_lt
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (α : ℝ) (hα_gt_one : 1 < α) :
    BddAbove
      (ρ.conditionalSandwichedRenyiValueSet hρ α (by linarith)
        (ne_of_gt hα_gt_one)) :=
  conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
    ρ hρ α (by linarith) (ne_of_gt hα_gt_one)
    (fun σ hσ =>
      conditionalSandwichedRenyiCandidate_le_log2_card_of_one_lt
        ρ hρ σ hσ α hα_gt_one)

/-- Candidate transport from a reverse channel on normalized references.

If a channel maps the output-side normalized pair
`(ρ₂, π_{A₂} ⊗ σ₂)` back to the input-side normalized pair
`(ρ₁, π_{A₁} ⊗ σ₁)`, then the already-proved high-parameter sandwiched Renyi DPI
gives the required reverse comparison of conditional candidates, up to the
explicit left-system dimension term.

This is the concrete high-`β` step consumed by the strict low-`α`
conditional-duality route. -/
theorem conditionalSandwichedRenyiCandidate_le_of_reverseChannel_normalizedReference
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (hρ₁ : ρ₁.matrix.PosDef)
    (σ₁ : State b₁) (hσ₁ : σ₁.matrix.PosDef)
    (ρ₂ : State (Prod a₂ b₂)) (hρ₂ : ρ₂.matrix.PosDef)
    (σ₂ : State b₂) (hσ₂ : σ₂.matrix.PosDef)
    (Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁))
    (hρΨ : Ψ.applyState ρ₂ = ρ₁)
    (hσΨ :
      Ψ.applyState
          ((@maximallyMixed a₂ _ _ (by
            rcases ρ₂.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod σ₂) =
        ((@maximallyMixed a₁ _ _ (by
          rcases ρ₁.nonempty with ⟨x⟩
          exact ⟨x.1⟩)).prod σ₁))
    (β : ℝ) (hβ_gt_one : 1 < β)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ)) :
    ρ₂.conditionalSandwichedRenyiCandidate hρ₂ σ₂ hσ₂ β
        (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ σ₁ hσ₁ β
        (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) := by
  haveI : Nonempty a₁ := by
    rcases ρ₁.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  haveI : Nonempty a₂ := by
    rcases ρ₂.nonempty with ⟨x⟩
    exact ⟨x.1⟩
  let ν₁ : State (Prod a₁ b₁) := (maximallyMixed a₁).prod σ₁
  let ν₂ : State (Prod a₂ b₂) := (maximallyMixed a₂).prod σ₂
  have hν₁ : ν₁.matrix.PosDef := by
    simpa [ν₁] using conditionalRenyi_normalizedReference_posDef ρ₁ σ₁ hσ₁
  have hν₂ : ν₂.matrix.PosDef := by
    simpa [ν₂] using conditionalRenyi_normalizedReference_posDef ρ₂ σ₂ hσ₂
  have hρΨ_pos : (Ψ.applyState ρ₂).matrix.PosDef := by
    rw [hρΨ]
    exact hρ₁
  have hνΨ_pos : (Ψ.applyState ν₂).matrix.PosDef := by
    rw [show Ψ.applyState ν₂ = ν₁ by simpa [ν₁, ν₂] using hσΨ]
    exact hν₁
  have hDPI_stmt :
      sandwichedRenyi_dataProcessing_channel_statement ρ₂ ν₂ Ψ
        hρ₂ hν₂ hρΨ_pos hνΨ_pos β (by linarith) (ne_of_gt hβ_gt_one) :=
    sandwichedRenyi_dataProcessing_channel_statement_of_one_lt_channel
      ρ₂ ν₂ Ψ hρ₂ hν₂ hρΨ_pos hνΨ_pos β hβ_gt_one
  have hDPI :
      sandwichedRenyi ρ₁ ν₁ hρ₁ hν₁ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤
        sandwichedRenyi ρ₂ ν₂ hρ₂ hν₂ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) := by
    unfold sandwichedRenyi_dataProcessing_channel_statement at hDPI_stmt
    simpa [ν₁, ν₂, hρΨ, hσΨ] using hDPI_stmt
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₂ hρ₂ σ₂ hσ₂ β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one)]
  rw [conditionalSandwichedRenyiCandidate_eq_log2_card_sub_sandwichedRenyi_normalizedReference
    ρ₁ hρ₁ σ₁ hσ₁ β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one)]
  simpa [ν₁, ν₂] using sub_le_sub hdim hDPI

/-- The upward conditional sandwiched Renyi duality statement is symmetric
under swapping the complementary systems and the Holder-dual exponents.

This is only an algebraic statement-layer bridge: it reuses a proved instance
of the source duality equality in one direction and flips the real equality.
It does not assert or prove the missing conditional-duality theorem itself. -/
theorem conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement ρ σ hρ hσ
        α β hα hβ hα1 hβ1 hab) :
    conditionalSandwichedRenyi_duality_pair_algebraic_statement
      (a := a) (b := c) (c := b) σ ρ hσ hρ
      β α hβ hα hβ1 hα1 (by simpa [add_comm] using hab) := by
  unfold conditionalSandwichedRenyi_duality_pair_algebraic_statement at hdual ⊢
  linarith

/-- Conditional-duality symmetry specialized to the low-`α` dual parameter
`β = α / (2α - 1)`.

This is the exact exponent bookkeeping needed by the `1 / 2 < α < 1` route:
once the conditional duality theorem is available in one direction, this lemma
turns it into the swapped complementary-system statement whose exponent lies in
the already-proved `β > 1` range. -/
theorem conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm_dualParameter
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement ρ σ hρ hσ
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)) :
    conditionalSandwichedRenyi_duality_pair_algebraic_statement
      (a := a) (b := c) (c := b) σ ρ hσ hρ
      (renyiDualParameter α) α
      (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
      (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
      (by
        simpa [add_comm] using
          renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm
      ρ σ hρ hσ α (renyiDualParameter α)
      (le_of_lt hα_half) (renyiDualParameter_half_le hα_half hα_lt_one)
      (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
      (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
      hdual

/-- Conditional-duality symmetry specialized to the dual parameter, starting
from the swapped complementary-system direction.

This is the direction used when the source proof supplies the high-`β`
conditional duality statement first: it converts
`H̃^↑_β(A|C) = -H̃^↑_α(A|B)` back to the low-`α` statement consumed by the
strict subunit monotonicity route. -/
theorem conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm_swappedDualParameter
    (ρ : State (Prod a b)) (σ : State (Prod a c))
    (hρ : ρ.matrix.PosDef) (hσ : σ.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := c) (c := b) σ ρ hσ hρ
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)) :
    conditionalSandwichedRenyi_duality_pair_algebraic_statement ρ σ hρ hσ
      α (renyiDualParameter α) (le_of_lt hα_half)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
      (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm
      σ ρ hσ hρ (renyiDualParameter α) α
      (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
      (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
      (by
        simpa [add_comm] using
          renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
      hdual

/-- Algebraic conditional-duality handoff for the low-`α` monotonicity route.

If two low-`α` conditional entropies are related to their complementary
high-`β` conditional entropies by upward sandwiched Renyi duality, then a
monotonicity inequality on the complementary `β > 1` side transfers to the
desired low-`α` inequality after negating both sides.

This theorem does not prove conditional Renyi duality or the high-`β`
monotonicity theorem; it isolates the exact algebraic step needed once those
source-backed ingredients are available. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse
    (ρ₁ ρ₂ : State (Prod a b)) (σ₁ σ₂ : State (Prod a c))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement ρ₁ σ₁ hρ₁ hσ₁
        α β hα hβ hα1 hβ1 hab)
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement ρ₂ σ₂ hρ₂ hσ₂
        α β hα hβ hα1 hβ1 hab)
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ β hβ hβ1 ≤
        conditionalSandwichedRenyi σ₁ hσ₁ β hβ hβ1) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α hα hα1 ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α hα hα1 := by
  unfold conditionalSandwichedRenyi_duality_pair_algebraic_statement at hdual₁ hdual₂
  linarith

/-- Heterogeneous version of the conditional-duality handoff.

The left subsystem may change under the operation being proved monotone
(for example a measurement map changes `A` to a classical output register).
The proof is still purely algebraic: two duality equalities plus the
complementary high-`β` inequality transfer across negation. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_heterogeneous
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α β : ℝ) (hα : 1 / 2 ≤ α) (hβ : 1 / 2 ≤ β)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hab : 1 / α + 1 / β = 2)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α β hα hβ hα1 hβ1 hab)
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α β hα hβ hα1 hβ1 hab)
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ β hβ hβ1 ≤
        conditionalSandwichedRenyi σ₁ hσ₁ β hβ hβ1) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α hα hα1 ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α hα hα1 := by
  unfold conditionalSandwichedRenyi_duality_pair_algebraic_statement at hdual₁ hdual₂
  linarith

/-- Conditional-duality handoff specialized to the strict low-`α` dual
parameter `β = α / (2α - 1)`.

This packages the exponent bookkeeping for the source range
`1 / 2 < α < 1`: the complementary side lies in the already-established
`β > 1` range, and a high-`β` reverse monotonicity inequality transfers to the
low-`α` side. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hhigh :
      conditionalSandwichedRenyi σ₂ hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        conditionalSandwichedRenyi σ₁ hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) :=
  conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_heterogeneous
    ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
    α (renyiDualParameter α)
    (le_of_lt hα_half)
    (renyiDualParameter_half_le hα_half hα_lt_one)
    (ne_of_lt hα_lt_one)
    (renyiDualParameter_ne_one hα_half hα_lt_one)
    (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one)
    hdual₁ hdual₂ hhigh

/-- Candidate-level sufficient condition for a high-parameter conditional
Renyi reverse inequality.

This is the `sSup` handoff needed by the strict low-`α` duality route: instead
of proving an abstract conditional-entropy inequality on the complementary
side, it is enough to bound every output side-information candidate by the
input conditional entropy. -/
theorem conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    (hcand :
      ∀ η : State b₂, ∀ hη : η.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η hη β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  haveI : Nonempty b₂ := by
    rcases ρ₂.nonempty with ⟨x⟩
    exact ⟨x.2⟩
  exact
    conditionalSandwichedRenyi_le_of_forall_candidate_le
      ρ₂ hρ₂ β hβ hβ1 hcand

/-- Candidate-transport sufficient condition for a high-parameter conditional
Renyi reverse inequality.

If every output side-information candidate can be bounded by one fixed input
candidate, then the output conditional entropy is bounded by the input
conditional entropy, provided the input candidate family is bounded above.
This is the concrete candidate-lift form consumed by the low-`α`
measurement/duality route. -/
theorem conditionalSandwichedRenyi_le_of_candidate_lift
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ : BddAbove (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β hβ hβ1))
    (hlift :
      ∀ η₂ : State b₂, ∀ hη₂ : η₂.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η₂ hη₂ β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  have hη₁_le :
      ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1 ≤
        ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 :=
    conditionalSandwichedRenyiCandidate_le_conditionalSandwichedRenyi_of_bddAbove
      ρ₁ hρ₁ η₁ hη₁ β hβ hβ1 hbdd₁
  exact
    conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ hβ1
      (fun η₂ hη₂ => le_trans (hlift η₂ hη₂) hη₁_le)

/-- High-parameter conditional reverse inequality from a family of reverse
channels on normalized references.

For every output side-information candidate `η₂`, assume there is a channel
that sends the output normalized pair `(ρ₂, π_{A₂} ⊗ η₂)` back to the fixed input
pair `(ρ₁, π_{A₁} ⊗ η₁)`. The high-`β` sandwiched Renyi DPI then supplies the
candidate lift required by `conditionalSandwichedRenyi_le_of_candidate_lift`. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ :
      BddAbove
        (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β (by linarith)
          (ne_of_gt hβ_gt_one)))
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_candidate_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β (by linarith) (ne_of_gt hβ_gt_one)
      η₁ hη₁ hbdd₁
      (fun η₂ hη₂ => by
        rcases hreverse η₂ hη₂ with ⟨Ψ, hρΨ, hηΨ⟩
        exact
          conditionalSandwichedRenyiCandidate_le_of_reverseChannel_normalizedReference
            ρ₁ hρ₁ η₁ hη₁ ρ₂ hρ₂ η₂ hη₂ Ψ hρΨ hηΨ
            β hβ_gt_one hdim)

/-- Concrete-bound version of
`conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift`.

This packages the exact data usually available in a proof sprint: a fixed input
candidate, a reverse-channel lift for every output candidate, and any finite
uniform upper bound on the input candidate family. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    {C : ℝ}
    (hinputBound :
      ∀ η₁ : State b₁, ∀ hη₁ : η₁.matrix.PosDef,
        ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β
          (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one) ≤ C)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  have hbdd₁ :
      BddAbove
        (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β (by linarith)
          (ne_of_gt hβ_gt_one)) :=
    conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
      ρ₁ hρ₁ β (by linarith) (ne_of_gt hβ_gt_one)
      (by
        intro η hη
        exact hinputBound η hη)
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁ hbdd₁ hdim hreverse

/-- Reverse-channel high-parameter conditional inequality with the input
boundedness side condition discharged by normalized-reference nonnegativity.

The remaining hypothesis is now the source-standard statement that every
ordinary sandwiched Renyi divergence
`D̃_β(ρ₁ ‖ π_A ⊗ η₁)` is nonnegative, rather than an arbitrary finite upper
bound on conditional candidates. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_nonneg
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (hinputNonneg :
      ∀ η₁' : State b₁, ∀ hη₁' : η₁'.matrix.PosDef,
        0 ≤ sandwichedRenyi ρ₁
          ((@maximallyMixed a₁ _ _ (by
            rcases ρ₁.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod η₁')
          hρ₁
          (conditionalRenyi_normalizedReference_posDef ρ₁ η₁' hη₁')
          β (lt_trans zero_lt_one hβ_gt_one) (ne_of_gt hβ_gt_one))
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one
      (C := log2 (Fintype.card a₁ : ℝ))
      (fun η₁' hη₁' =>
        conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
          ρ₁ hρ₁ η₁' hη₁' β (lt_trans zero_lt_one hβ_gt_one)
          (ne_of_gt hβ_gt_one) (hinputNonneg η₁' hη₁'))
      η₁ hη₁ hdim hreverse

/-- Reverse-channel high-parameter conditional inequality with no external
boundedness hypothesis.

The input candidate family is bounded by `log₂ |A₁|`, using ordinary
sandwiched Renyi nonnegativity in the proved `β > 1` range. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ b₂) (Prod a₁ b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁
      (conditionalSandwichedRenyiValueSet_bddAbove_log2_card_of_one_lt
        ρ₁ hρ₁ β hβ_gt_one)
      hdim hreverse

/-- Same-left-system form of the high-parameter reverse-channel conditional
inequality.

When the two conditional states use the same left system, the dimension
comparison required by the general lift is reflexive. This is the form needed
for channel DPI reductions whose purification/duality step does not change the
reference system. -/
theorem conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_sameLeft_of_one_lt
    {a b₁ b₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ_gt_one : 1 < β)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State b₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a b₂) (Prod a b₁),
          Ψ.applyState ρ₂ = ρ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases ρ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases ρ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β (by linarith) (ne_of_gt hβ_gt_one) ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β (by linarith) (ne_of_gt hβ_gt_one) := by
  exact
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ_gt_one η₁ hη₁ le_rfl hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side.

This is the reusable route behind the measurement-specific theorem below:
conditional duality reduces the strict low-`α` comparison to a high-`β`
conditional reverse inequality, and the latter is discharged by the already
proved `β > 1` sandwiched Renyi DPI applied to normalized conditional
references. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ η₁' : State c₁, ∀ hη₁' : η₁'.matrix.PosDef,
        σ₁.conditionalSandwichedRenyiCandidate hσ₁ η₁' hη₁'
          (renyiDualParameter α)
          (lt_trans zero_lt_one (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)) ≤ C)
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_input_bound
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      hinputBound η₁ hη₁ hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Strict low-`α` conditional monotonicity with the complementary
high-`β` input boundedness reduced to ordinary normalized-reference
nonnegativity.

This is the same duality/reverse-channel route as
`conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound`,
but it packages the input candidate bound using the identity
`candidate = log₂ |A| - D̃_β(σ₁ ‖ π_A ⊗ η₁)`. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hinputNonneg :
      ∀ η₁' : State c₁, ∀ hη₁' : η₁'.matrix.PosDef,
        0 ≤ sandwichedRenyi σ₁
          ((@maximallyMixed a₁ _ _ (by
            rcases σ₁.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod η₁')
          hσ₁
          (conditionalRenyi_normalizedReference_posDef σ₁ η₁' hη₁')
          (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂
      (C := log2 (Fintype.card a₁ : ℝ))
      (fun η₁' hη₁' =>
        conditionalSandwichedRenyiCandidate_le_log2_card_of_normalizedReference_nonneg
          σ₁ hσ₁ η₁' hη₁' (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one))
          (hinputNonneg η₁' hη₁'))
      η₁ hη₁ hdim hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction, with the high-`β` input candidate boundedness
discharged internally by `β > 1` sandwiched Renyi nonnegativity. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift_of_one_lt
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      η₁ hη₁ hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Same-left-system strict low-`α` conditional monotonicity from conditional
duality and a reverse-channel construction.

This packages the common case where the duality/recovery step preserves the
left reference system, so the dimension comparison in the general lift is
automatic. The remaining nontrivial assumptions are the conditional duality
statements and the explicit reverse-channel family on the complementary side. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
    {a b₁ c₁ b₂ c₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (σ₁ : State (Prod a c₁)) (σ₂ : State (Prod a c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a c₂) (Prod a c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ η₁ hη₁ le_rfl hreverse

/-- Same-left-system strict low-`α` conditional monotonicity when the
conditional-duality inputs are supplied in the swapped high-`β` direction.

This is a convenience bridge for source proofs that state duality as
`H̃^↑_β(A|C) = -H̃^↑_α(A|B)`. The theorem converts both duality statements to
the low-`α` direction and then applies the same-left reverse-channel lift. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
    {a b₁ c₁ b₂ c₂ : Type*}
    [Fintype a] [DecidableEq a] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a b₁)) (ρ₂ : State (Prod a b₂))
    (σ₁ : State (Prod a c₁)) (σ₂ : State (Prod a c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := c₁) (c := b₁) σ₁ ρ₁ hσ₁ hρ₁
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := c₂) (c := b₂) σ₂ ρ₂ hσ₂ hρ₂
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a c₂) (Prod a c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one
      (conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm_swappedDualParameter
        ρ₁ σ₁ hρ₁ hσ₁ α hα_half hα_lt_one hdual₁)
      (conditionalSandwichedRenyi_duality_pair_algebraic_statement.symm_swappedDualParameter
        ρ₂ σ₂ hρ₂ hσ₂ α hα_half hα_lt_one hdual₂)
      η₁ hη₁ hreverse

/-- Strict low-`α` conditional monotonicity from conditional duality and a
reverse-channel construction, using a raw boundedness witness for the input
high-`β` candidate value set. -/
theorem conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift
    {a₁ b₁ c₁ a₂ b₂ c₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype c₂] [DecidableEq c₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (σ₁ : State (Prod a₁ c₁)) (σ₂ : State (Prod a₂ c₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (hσ₁ : σ₁.matrix.PosDef) (hσ₂ : σ₂.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdual₁ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₁) (b := b₁) (c := c₁) ρ₁ σ₁ hρ₁ hσ₁
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdual₂ :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a₂) (b := b₂) (c := c₂) ρ₂ σ₂ hρ₂ hσ₂
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (η₁ : State c₁) (hη₁ : η₁.matrix.PosDef)
    (hbdd₁ :
      BddAbove
        (σ₁.conditionalSandwichedRenyiValueSet hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hdim : log2 (Fintype.card a₂ : ℝ) ≤ log2 (Fintype.card a₁ : ℝ))
    (hreverse :
      ∀ η₂ : State c₂, η₂.matrix.PosDef →
        ∃ Ψ : Channel (Prod a₂ c₂) (Prod a₁ c₁),
          Ψ.applyState σ₂ = σ₁ ∧
            Ψ.applyState
                ((@maximallyMixed a₂ _ _ (by
                  rcases σ₂.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod η₂) =
              ((@maximallyMixed a₁ _ _ (by
                rcases σ₁.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod η₁)) :
    conditionalSandwichedRenyi ρ₂ hρ₂ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) ≥
      conditionalSandwichedRenyi ρ₁ hρ₁ α (le_of_lt hα_half)
        (ne_of_lt hα_lt_one) := by
  have hβgt : 1 < renyiDualParameter α :=
    renyiDualParameter_gt_one hα_half hα_lt_one
  have hhigh_raw :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (by linarith) (ne_of_gt hβgt) :=
    conditionalSandwichedRenyi_le_of_reverseChannel_normalizedReference_lift
      σ₁ σ₂ hσ₁ hσ₂ (renyiDualParameter α) hβgt
      η₁ hη₁ (by simpa using hbdd₁) hdim hreverse
  have hhigh :
      σ₂.conditionalSandwichedRenyi hσ₂ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σ₁.conditionalSandwichedRenyi hσ₁ (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) := by
    simpa using hhigh_raw
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ₁ ρ₂ σ₁ σ₂ hρ₁ hρ₂ hσ₁ hσ₂
      α hα_half hα_lt_one hdual₁ hdual₂ hhigh

/-- Candidate transport with a concrete uniform upper bound for the input
candidate family.

This variant avoids carrying a raw `BddAbove` proof through later DPI route
lemmas. A source proof can provide any finite uniform upper bound on the input
side-information candidates, then use the fixed-candidate lift to obtain the
high-parameter conditional reverse inequality. -/
theorem conditionalSandwichedRenyi_le_of_candidate_lift_of_forall_input_candidate_le
    {a₁ b₁ a₂ b₂ : Type*}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    (ρ₁ : State (Prod a₁ b₁)) (ρ₂ : State (Prod a₂ b₂))
    (hρ₁ : ρ₁.matrix.PosDef) (hρ₂ : ρ₂.matrix.PosDef)
    (β : ℝ) (hβ : 1 / 2 ≤ β) (hβ1 : β ≠ 1)
    {C : ℝ}
    (hinputBound :
      ∀ η₁ : State b₁, ∀ hη₁ : η₁.matrix.PosDef,
        ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1 ≤ C)
    (η₁ : State b₁) (hη₁ : η₁.matrix.PosDef)
    (hlift :
      ∀ η₂ : State b₂, ∀ hη₂ : η₂.matrix.PosDef,
        ρ₂.conditionalSandwichedRenyiCandidate hρ₂ η₂ hη₂ β (by linarith) hβ1 ≤
          ρ₁.conditionalSandwichedRenyiCandidate hρ₁ η₁ hη₁ β (by linarith) hβ1) :
    ρ₂.conditionalSandwichedRenyi hρ₂ β hβ hβ1 ≤
      ρ₁.conditionalSandwichedRenyi hρ₁ β hβ hβ1 := by
  have hbdd₁ :
      BddAbove (ρ₁.conditionalSandwichedRenyiValueSet hρ₁ β hβ hβ1) :=
    conditionalSandwichedRenyiValueSet_bddAbove_of_forall_candidate_le
      ρ₁ hρ₁ β hβ hβ1 hinputBound
  exact
    conditionalSandwichedRenyi_le_of_candidate_lift
      ρ₁ ρ₂ hρ₁ hρ₂ β hβ hβ1 η₁ hη₁ hbdd₁ hlift

/-- Measurement-map monotonicity obtained from conditional duality and the
complementary high-`β` reverse inequality.

This is the statement-level shell for the strict low-`α` measurement route:
once the two conditional-duality instances and the complementary `β > 1`
monotonicity inequality are available, the registered measurement monotonicity
statement follows without any further analytic work. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hhigh :
      conditionalSandwichedRenyi σOut hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        conditionalSandwichedRenyi σIn hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_high_reverse_dualParameter
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality and a
candidate-level complementary high-`β` bound.

This removes one abstraction layer from the low-`α` route: the remaining
high-parameter task can be proved by checking every full-rank side-information
candidate of the complementary output state. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_candidate_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hcand :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
            (renyiDualParameter_half_le hα_half hα_lt_one)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_forall_candidate_le_conditional
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      hcand
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hMUnit hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality, a fixed
candidate transport, and a concrete uniform upper bound on the input
complementary candidate family.

This is the no-raw-`BddAbove` version of the candidate-lift route. It is useful
when the remaining high-`β` source proof naturally supplies a numerical
candidate bound rather than an order-theoretic value-set boundedness proof. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift_of_input_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        σIn.conditionalSandwichedRenyiCandidate hσIn ηIn' hηIn'
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤ C)
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hlift :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyiCandidate hσIn ηIn hηIn
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_candidate_lift_of_forall_input_candidate_le
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      hinputBound ηIn hηIn hlift
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hMUnit hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side.

Compared with
`measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift_of_input_bound`,
this theorem discharges the candidate lift using the high-`β` sandwiched Renyi
DPI for normalized conditional references. The remaining source-level
obligations are the two conditional-duality instances, an input candidate
boundedness witness, and the reverse channel family on complementary systems. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_input_bound
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    {C : ℝ}
    (hinputBound :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        σIn.conditionalSandwichedRenyiCandidate hσIn ηIn' hηIn'
            (renyiDualParameter α)
            (lt_trans zero_lt_one
              (renyiDualParameter_gt_one hα_half hα_lt_one))
            (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)) ≤ C)
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_bound
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      hinputBound ηIn hηIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction, with the input high-`β` candidate bound reduced
to ordinary nonnegativity against normalized conditional references.

This is the measurement-facing version of
`conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg`.
It leaves the proof sprint with a sharper remaining blocker: prove
`D̃_β(σIn ‖ π_A ⊗ η) ≥ 0` for the complementary high-`β` states, rather than
provide an arbitrary uniform candidate bound. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_input_nonneg
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hinputNonneg :
      ∀ ηIn' : State d, ∀ hηIn' : ηIn'.matrix.PosDef,
        0 ≤ sandwichedRenyi σIn
          ((@maximallyMixed a _ _ (by
            rcases σIn.nonempty with ⟨x⟩
            exact ⟨x.1⟩)).prod ηIn')
          hσIn
          (conditionalRenyi_normalizedReference_posDef σIn ηIn' hηIn')
          (renyiDualParameter α)
          (lt_trans zero_lt_one
            (renyiDualParameter_gt_one hα_half hα_lt_one))
          (ne_of_gt (renyiDualParameter_gt_one hα_half hα_lt_one)))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_input_nonneg
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      hinputNonneg ηIn hηIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction, with no external input boundedness hypothesis.

The high-`β` input candidate family is bounded internally by the proved
ordinary sandwiched Renyi nonnegativity in the `β > 1` range. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hdim hreverse

/-- Same-left-system measurement form of the strict low-`α`
duality/reverse-channel route.

This specializes the measurement-facing theorem to measurements whose output
left register is the same type as the input left register, such as same-system
pinching measurements. In that case the dimension comparison in the general
measurement theorem is discharged by reflexivity. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift_sameLeft_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM a a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod a e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod a e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hreverse

/-- Same-left-system measurement monotonicity when the conditional-duality
inputs are supplied in the swapped high-`β` direction.

This is the measurement-facing companion of
`conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt`.
It is tailored for same-system measurements, including pinching measurements,
whose source duality proof may naturally present the complementary high-`β`
entropy first. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM a a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod a e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := d) (c := b) σIn ρ hσIn hρ
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := e) (c := b) σOut (measureSubsystemState M ρ) hσOut hρM
        (renyiDualParameter α) α
        (renyiDualParameter_half_le hα_half hα_lt_one) (le_of_lt hα_half)
        (renyiDualParameter_ne_one hα_half hα_lt_one) (ne_of_lt hα_lt_one)
        (by
          simpa [add_comm] using
            renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod a e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed a _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_swappedDuality_and_reverseChannel_lift_sameLeft_of_one_lt
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut
      ηIn hηIn hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
reverse-channel construction on the complementary high-`β` side, using a raw
boundedness witness for the input complementary candidate value set. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_reverseChannel_lift
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hbddIn :
      BddAbove
        (σIn.conditionalSandwichedRenyiValueSet hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hdim : log2 (Fintype.card c : ℝ) ≤ log2 (Fintype.card a : ℝ))
    (hreverse :
      ∀ ηOut : State e, ηOut.matrix.PosDef →
        ∃ Ψ : Channel (Prod c e) (Prod a d),
          Ψ.applyState σOut = σIn ∧
            Ψ.applyState
                ((@maximallyMixed c _ _ (by
                  rcases σOut.nonempty with ⟨x⟩
                  exact ⟨x.1⟩)).prod ηOut) =
              ((@maximallyMixed a _ _ (by
                rcases σIn.nonempty with ⟨x⟩
                exact ⟨x.1⟩)).prod ηIn)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  unfold measurementMap_conditionalRenyi_monotonicity_statement
  exact
    conditionalSandwichedRenyi_low_monotonicity_of_duality_and_reverseChannel_lift
      ρ (measureSubsystemState M ρ) σIn σOut hρ hρM hσIn hσOut
      α hα_half hα_lt_one hdualIn hdualOut ηIn hηIn hbddIn hdim hreverse

/-- Strict low-`α` measurement monotonicity from conditional duality and a
single candidate-transport construction on the complementary high-`β` side.

This is the form closest to the source proof obligation: for every output
side-information candidate, construct or bound it by one fixed input
side-information candidate. -/
theorem measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_candidate_lift
    {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
    (ρ : State (Prod a b)) (hρ : ρ.matrix.PosDef)
    (M : POVM c a) (hMUnit : measurementMapDoesNotEnlargeUnit M) (hρM : (measureSubsystemState M ρ).matrix.PosDef)
    (σIn : State (Prod a d)) (σOut : State (Prod c e))
    (hσIn : σIn.matrix.PosDef) (hσOut : σOut.matrix.PosDef)
    (α : ℝ) (hα_half : 1 / 2 < α) (hα_lt_one : α < 1)
    (hdualIn :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := a) (b := b) (c := d) ρ σIn hρ hσIn
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (hdualOut :
      conditionalSandwichedRenyi_duality_pair_algebraic_statement
        (a := c) (b := b) (c := e) (measureSubsystemState M ρ) σOut
        hρM hσOut
        α (renyiDualParameter α) (le_of_lt hα_half)
        (renyiDualParameter_half_le hα_half hα_lt_one)
        (ne_of_lt hα_lt_one) (renyiDualParameter_ne_one hα_half hα_lt_one)
        (renyiDualParameter_inv_add_inv_eq_two_of_half_lt hα_half hα_lt_one))
    (ηIn : State d) (hηIn : ηIn.matrix.PosDef)
    (hbddIn :
      BddAbove
        (σIn.conditionalSandwichedRenyiValueSet hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one)))
    (hlift :
      ∀ ηOut : State e, ∀ hηOut : ηOut.matrix.PosDef,
        σOut.conditionalSandwichedRenyiCandidate hσOut ηOut hηOut
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
          σIn.conditionalSandwichedRenyiCandidate hσIn ηIn hηIn
            (renyiDualParameter α) (by
              have hβ := renyiDualParameter_half_le hα_half hα_lt_one
              linarith)
            (renyiDualParameter_ne_one hα_half hα_lt_one)) :
    measurementMap_conditionalRenyi_monotonicity_statement ρ hρ M hMUnit hρM
      α (le_of_lt hα_half) (ne_of_lt hα_lt_one) := by
  have hhigh :
      σOut.conditionalSandwichedRenyi hσOut (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) ≤
        σIn.conditionalSandwichedRenyi hσIn (renyiDualParameter α)
          (renyiDualParameter_half_le hα_half hα_lt_one)
          (renyiDualParameter_ne_one hα_half hα_lt_one) :=
    conditionalSandwichedRenyi_le_of_candidate_lift
      σIn σOut hσIn hσOut
      (renyiDualParameter α)
      (renyiDualParameter_half_le hα_half hα_lt_one)
      (renyiDualParameter_ne_one hα_half hα_lt_one)
      ηIn hηIn hbddIn hlift
  exact
    measurementMap_conditionalRenyi_monotonicity_statement_of_dualParameter_duality_and_high_reverse
      ρ hρ M hMUnit hρM σIn σOut hσIn hσOut α hα_half hα_lt_one
      hdualIn hdualOut hhigh

end State

end

end QIT
