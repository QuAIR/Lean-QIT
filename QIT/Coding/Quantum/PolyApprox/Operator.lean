/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.Quantum.PolyApprox.Basic
public import QIT.Util.Matrix.JointDiagonalization

/-!
# Operator bounds for the polynomial projector approximation

The commuting local defects have joint eigenvalues zero or one. Their sum
counts the active defects, and their complementary product is the tensor-power
projector [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:533-533].
The scalar grid bound therefore gives the support identities and operator-norm
estimate [BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530].
-/

@[expose] public section

namespace QIT.QuantumPolyApprox

noncomputable section

open scoped QIT.Matrix Matrix.Norms.L2Operator

universe u
variable {b e : Type u} [Fintype b] [Fintype e] [DecidableEq b] [DecidableEq e]

/-- Regrouping preserves the entrywise tensor power. -/
theorem pairReindex_tensorPowMatrixPi (P : CMatrix (b × e)) (n : ℕ) :
    pairReindex n (TensorPower.tensorPowMatrixPi P n) =
      TensorPower.tensorPowMatrixPair P n := by
  rfl

/-- Local defects commute on independent registers. -/
theorem localDefect_comm (P : CMatrix (b × e)) {n : ℕ} (i j : Fin (n + 1)) :
    Commute (localDefect P i) (localDefect P j) :=
  (WireFam.deltaAt_comm i j P).map (pairReindex (n + 1))

/-- Local defects retain idempotence after regrouping the registers. -/
theorem localDefect_idempotent {P : CMatrix (b × e)} (hP : P * P = P)
    {n : ℕ} (i : Fin (n + 1)) :
    localDefect P i * localDefect P i = localDefect P i := by
  simpa only [localDefect, map_mul] using
    congrArg (pairReindex (n + 1)) (WireFam.deltaAt_idempotent i hP)

/-- Local defects retain Hermitian symmetry after regrouping the registers. -/
theorem localDefect_isHermitian {P : CMatrix (b × e)} (hP : P.IsHermitian)
    {n : ℕ} (i : Fin (n + 1)) : (localDefect P i).IsHermitian :=
  (WireFam.deltaAt_isHermitian i hP).reindex
    (Equiv.arrowProdEquivProdArrow (Fin (n + 1)) (fun _ => b) (fun _ => e))

/-- The binomial polynomial in the counting operator is the sum over subsets
of independent registers [BeigiTomamichel2026BlowingUp,
strong_converse_blowing_up.tex:554-566]. -/
theorem choose_countingOperator_eq_sum_noncommProd (P : CMatrix (b × e))
    (hP : P * P = P) (n s : ℕ) :
    Ring.choose (countingOperator P (n + 1)) s =
      ∑ S ∈ ((Finset.univ : Finset (Fin (n + 1))).powersetCard s).attach,
        S.val.noncommProd (localDefect P)
          (fun i _ j _ _ => localDefect_comm P i j) := by
  simpa only [countingOperator] using
    QIT.choose_sum_idempotent_eq_sum_noncommProd Finset.univ (localDefect P)
      (fun i _ j _ => localDefect_comm P i j)
      (fun i _ => localDefect_idempotent hP i) s

/-- The tensor-power projector is the product of the complementary local defects. -/
theorem tensorPow_eq_noncommProd_one_sub_localDefect (P : CMatrix (b × e)) (n : ℕ) :
    TensorPower.tensorPowMatrixPair P (n + 1) =
      Finset.univ.noncommProd (fun i : Fin (n + 1) => 1 - localDefect P i)
        (fun i _ j _ _ =>
          ((Commute.one_left _).sub_left
            ((Commute.one_right _).sub_right (localDefect_comm P i j)))) := by
  rw [← pairReindex_tensorPowMatrixPi, TensorPower.tensorPowMatrixPi_eq_prod_liftAt,
    Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro i _
  simp only [localDefect, WireFam.deltaAt, map_sub, map_one, sub_sub_cancel]


private theorem noncommProd_diagonal {m ι : Type*} [Fintype m] [DecidableEq m]
    (s : Finset ι) (d : ι → m → ℂ)
    (hc : (s : Set ι).Pairwise (Function.onFun Commute (fun i => Matrix.diagonal (d i)))) :
    s.noncommProd (fun i => Matrix.diagonal (d i)) hc =
      Matrix.diagonal (fun a => ∏ i ∈ s, d i a) := by
  have h := Finset.map_noncommProd s d (fun _ _ _ _ _ => Commute.all _ _)
    (Matrix.diagonalAlgHom ℂ)
  rw [Finset.noncommProd_eq_prod] at h
  refine h.symm.trans ?_
  change Matrix.diagonal (s.prod d) = Matrix.diagonal _
  congr 1
  funext a
  exact Finset.prod_apply a s d

/-- A common eigenvalue of an idempotent Hermitian family is zero or one. -/
private theorem jointEigenvalue_zero_or_one {m ι : Type*}
    [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]
    {A : ι → CMatrix m} (hh : ∀ i, (A i).IsHermitian)
    (hc : Pairwise (Function.onFun Commute A)) (hi : ∀ i, A i * A i = A i)
    (i : ι) (a : m) :
    jointMatrixEigenvalues hh hc i a = 0 ∨ jointMatrixEigenvalues hh hc i a = 1 := by
  let F := Unitary.conjStarAlgAut ℂ _ (star (jointUnitary hh hc))
  have h := congrArg F (hi i)
  simp only [map_mul, F, conjStarAlgAut_star_jointUnitary, Matrix.diagonal_mul_diagonal] at h
  have he := congrArg (fun M : CMatrix m => M a a) h
  simp only [Matrix.diagonal_apply_eq, Function.comp_apply] at he
  have hr : jointMatrixEigenvalues hh hc i a * jointMatrixEigenvalues hh hc i a =
      jointMatrixEigenvalues hh hc i a := by exact_mod_cast he
  have hz : jointMatrixEigenvalues hh hc i a * (jointMatrixEigenvalues hh hc i a - 1) = 0 := by
    nlinarith [hr]
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

private theorem counting_diagonal {P : CMatrix (b × e)} (hPh : P.IsHermitian)
    (hPi : P * P = P) (n : ℕ) :
    ∃ U : unitary (CMatrix ((Fin (n + 1) → b) × (Fin (n + 1) → e))),
      ∃ k : ((Fin (n + 1) → b) × (Fin (n + 1) → e)) → ℕ,
        (∀ a, k a ≤ n + 1) ∧
        Unitary.conjStarAlgAut ℂ _ U (countingOperator P (n + 1)) =
          Matrix.diagonal (fun a => (k a : ℂ)) ∧
        Unitary.conjStarAlgAut ℂ _ U (TensorPower.tensorPowMatrixPair P (n + 1)) =
          Matrix.diagonal (fun a => if k a = 0 then 1 else 0) := by
  classical
  let A := fun i : Fin (n + 1) => localDefect P i
  have hh : ∀ i, (A i).IsHermitian := localDefect_isHermitian hPh
  have hc : Pairwise (Function.onFun Commute A) := fun i j _ => localDefect_comm P i j
  let d := jointMatrixEigenvalues hh hc
  let U := star (jointUnitary hh hc)
  let F := Unitary.conjStarAlgAut ℂ _ U
  let active := fun a => Finset.univ.filter (fun i => d i a = 1)
  let k := fun a => (active a).card
  have hd (i : Fin (n + 1)) (a) : d i a = 0 ∨ d i a = 1 :=
    jointEigenvalue_zero_or_one hh hc (localDefect_idempotent hPi) i a
  have hF (i : Fin (n + 1)) : F (A i) = Matrix.diagonal (fun a => (d i a : ℂ)) :=
    conjStarAlgAut_star_jointUnitary hh hc i
  have hsum (a) : (∑ i, (d i a : ℂ)) = (k a : ℂ) := by
    have he (i : Fin (n + 1)) : (d i a : ℂ) = if d i a = 1 then 1 else 0 := by
      rcases hd i a with h | h <;> simp [h]
    simp only [he, Finset.sum_boole, k, active]
  refine ⟨U, k, ?_, ?_, ?_⟩
  · intro a
    exact (Finset.card_filter_le _ _).trans (by simp)
  · change F (∑ i, A i) = _
    have h := conjStarAlgAut_star_jointUnitary_sum hh hc (fun _ => (1 : ℂ))
    simp only [one_smul, one_mul] at h
    change F (∑ i, A i) = Matrix.diagonal (fun a => ∑ i, (d i a : ℂ)) at h
    simpa only [hsum] using h
  · rw [tensorPow_eq_noncommProd_one_sub_localDefect]
    refine (Finset.map_noncommProd _ _ _ F).trans ?_
    have hcomplement (i : Fin (n + 1)) : F (1 - A i) =
        Matrix.diagonal (fun a => 1 - (d i a : ℂ)) := by
      rw [map_sub, map_one, hF, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    have he := Finset.noncommProd_congr rfl (fun i (_ : i ∈ Finset.univ) => hcomplement i)
      (fun i _ j _ _ =>
        (((Commute.one_left _).sub_left
          ((Commute.one_right _).sub_right (localDefect_comm P i j)))).map F)
    rw [he]
    refine (noncommProd_diagonal _ _ _).trans ?_
    congr 1
    funext a
    by_cases hk : k a = 0
    · rw [ite_eq_left hk]
      apply Finset.prod_eq_one
      intro i _
      have hnot : d i a ≠ 1 := by
        intro hi
        have : i ∈ active a := by simp [active, hi]
        have hempty : active a = ∅ := Finset.card_eq_zero.mp hk
        simp [hempty] at this
      rcases hd i a with hi | hi
      · simp [hi]
      · exact False.elim (hnot hi)
    · rw [ite_eq_right hk]
      have hne : (active a).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hk)
      obtain ⟨i, hi⟩ := hne
      have hi' : d i a = 1 := (Finset.mem_filter.mp hi).2
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi'])


private theorem aeval_real_eq_complex {m : Type*} [Fintype m] [DecidableEq m]
    (p : Polynomial ℝ) (M : CMatrix m) :
    Polynomial.aeval M p = Polynomial.aeval M (p.map (algebraMap ℝ ℂ)) :=
  Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℝ ℂ _).symm p M

private theorem aeval_real_diagonal {m : Type*} [Fintype m] [DecidableEq m]
    (p : Polynomial ℝ) (d : m → ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun a => (d a : ℂ))) p =
      Matrix.diagonal (fun a => ((p.eval (d a) : ℝ) : ℂ)) := by
  rw [aeval_real_eq_complex, QIT.aeval_diagonal]
  congr 1
  funext a
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) (d a)

private theorem conj_aeval_real {m : Type*} [Fintype m] [DecidableEq m]
    (U : unitary (CMatrix m)) (p : Polynomial ℝ) (M : CMatrix m) :
    Unitary.conjStarAlgAut ℂ _ U (Polynomial.aeval M p) =
      Polynomial.aeval (Unitary.conjStarAlgAut ℂ _ U M) p := by
  rw [aeval_real_eq_complex p M, ← Polynomial.aeval_algHom_apply,
    ← aeval_real_eq_complex]

private theorem approximation_diagonal {P : CMatrix (b × e)}
    (p : Polynomial ℝ) {n : ℕ}
    (U : unitary (CMatrix ((Fin (n + 1) → b) × (Fin (n + 1) → e))))
    (k : ((Fin (n + 1) → b) × (Fin (n + 1) → e)) → ℕ)
    (hL : Unitary.conjStarAlgAut ℂ _ U (countingOperator P (n + 1)) =
      Matrix.diagonal (fun a => (k a : ℂ))) :
    Unitary.conjStarAlgAut ℂ _ U (projectorApproximation p P (n + 1)) =
      Matrix.diagonal (fun a => ((p.eval (k a : ℝ) : ℝ) : ℂ)) := by
  rw [projectorApproximation, conj_aeval_real, hL]
  convert aeval_real_diagonal p (fun a => (k a : ℝ)) using 1

/-- The polynomial approximation fixes the tensor-power projector on the right
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530]. -/
theorem projectorApproximation_mul_tensorPow {P : CMatrix (b × e)}
    (hPh : P.IsHermitian) (hPi : P * P = P) (p : Polynomial ℝ)
    (hp : p.eval 0 = 1) (n : ℕ) :
    projectorApproximation p P (n + 1) * TensorPower.tensorPowMatrixPair P (n + 1) =
      TensorPower.tensorPowMatrixPair P (n + 1) := by
  classical
  obtain ⟨U, k, _, hL, hT⟩ := counting_diagonal hPh hPi n
  have hinj : Function.Injective (Unitary.conjStarAlgAut ℂ _ U) :=
    (Unitary.conjStarAlgAut ℂ _ U).injective
  apply hinj
  rw [map_mul, approximation_diagonal p U k hL, hT, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hk : k a = 0 <;> simp [hk, hp]

/-- The polynomial approximation fixes the tensor-power projector on the left
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530]. -/
theorem tensorPow_mul_projectorApproximation {P : CMatrix (b × e)}
    (hPh : P.IsHermitian) (hPi : P * P = P) (p : Polynomial ℝ)
    (hp : p.eval 0 = 1) (n : ℕ) :
    TensorPower.tensorPowMatrixPair P (n + 1) * projectorApproximation p P (n + 1) =
      TensorPower.tensorPowMatrixPair P (n + 1) := by
  classical
  obtain ⟨U, k, _, hL, hT⟩ := counting_diagonal hPh hPi n
  have hinj : Function.Injective (Unitary.conjStarAlgAut ℂ _ U) :=
    (Unitary.conjStarAlgAut ℂ _ U).injective
  apply hinj
  rw [map_mul, approximation_diagonal p U k hL, hT, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hk : k a = 0 <;> simp [hk, hp]

/-- A scalar error bound on the nonzero integer grid gives the operator error
of the tensor-power projector approximation
[BeigiTomamichel2026BlowingUp, strong_converse_blowing_up.tex:522-530]. -/
theorem norm_projectorApproximation_sub_le {P : CMatrix (b × e)}
    (hPh : P.IsHermitian) (hPi : P * P = P) (p : Polynomial ℝ)
    (hp : p.eval 0 = 1) (n : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hgrid : ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 → |p.eval (k : ℝ)| ≤ η) :
    ‖projectorApproximation p P (n + 1) - TensorPower.tensorPowMatrixPair P (n + 1)‖ ≤ η := by
  classical
  obtain ⟨U, k, hk, hL, hT⟩ := counting_diagonal hPh hPi n
  rw [← norm_conjStarAlgAut U, map_sub, approximation_diagonal p U k hL, hT,
    Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro a
  by_cases hka : k a = 0
  · simpa [hka, hp] using hη
  · simpa [hka, Complex.norm_real, Real.norm_eq_abs] using
      hgrid (k a) (Nat.one_le_iff_ne_zero.mpr hka) (hk a)

end
end QIT.QuantumPolyApprox
