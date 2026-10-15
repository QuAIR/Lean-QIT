/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Channels.CompleteAdmissibility

/-!
# Deterministic superchannels

A superchannel is a higher-order linear map on input-first Choi operators that
sends quantum channels to quantum channels deterministically
[Chiribella2008Supermaps, VersioneArchivio.tex:132-134]. Linearity is carried by
the `MatrixMap` carrier itself, and complete positivity is not a one-system
condition: the transformation must remain completely positive when applied
jointly with the identity supermap on arbitrary finite ancillary input and
output systems [Chiribella2008Supermaps, VersioneArchivio.tex:143-150].

The reference orders Choi operators with output spaces first, while this
library orders them input-first; `partialTraceB` plays the role of the output
partial trace in the reference's normalization. This module names the
deterministic superchannel predicate, forwards the stabilization API, and
proves that channel preservation on every finite joint input is equivalent to
complete deterministic admissibility. The equivalence uses an explicit
output-flag completion of an operation Choi operator to a channel Choi
operator.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Matrix

namespace QIT.HigherOrder

universe u v w x y z u' v'

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
variable {r : Type y} {s : Type z}
  [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]

/-- A deterministic superchannel: a linear higher-order map that is completely
admissible on quantum operations and preserves channels under every finite
ancillary extension. Linearity is carried by the `MatrixMap` carrier. -/
def IsDeterministicSuperchannel (S : MatrixMap (a × b) (c × d)) : Prop :=
  IsCompletelyDeterministic.{u, v, w, x, y, z} S

/-- The deterministic superchannel predicate is deterministic complete
admissibility. -/
theorem isDeterministicSuperchannel_iff {S : MatrixMap (a × b) (c × d)} :
    IsDeterministicSuperchannel.{u, v, w, x, y, z} S ↔
      IsCompletelyDeterministic.{u, v, w, x, y, z} S :=
  Iff.rfl

/-- A deterministic superchannel sends every channel with finite ancillary
wires to a channel. -/
def IsDeterministicSuperchannel.channel {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u, v, w, x, y, z} S)
    (N : Channel (a × r) (b × s)) : Channel (c × r) (d × s) :=
  IsCompletelyDeterministic.channel hS N

/-- A deterministic superchannel sends every trace-nonincreasing operation with
finite ancillary wires to a trace-nonincreasing operation. -/
theorem IsDeterministicSuperchannel.operation {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u, v, w, x, y, z} S)
    (Φ : MatrixMap (a × r) (b × s)) (hΦ : MatrixMap.TraceNonincreasingCP Φ) :
    MatrixMap.TraceNonincreasingCP (ancillaryAction S Φ) :=
  (isDeterministicSuperchannel_iff.mp hS).1.operation Φ hΦ

/-- Deterministic superchannels compose. -/
theorem IsDeterministicSuperchannel.comp {e : Type u'} {f : Type v'}
    [Fintype e] [DecidableEq e] [Fintype f] [DecidableEq f]
    {T : MatrixMap (c × d) (e × f)} {S : MatrixMap (a × b) (c × d)}
    (hT : IsDeterministicSuperchannel.{w, x, u', v', y, z} T)
    (hS : IsDeterministicSuperchannel.{u, v, w, x, y, z} S) :
    IsDeterministicSuperchannel.{u, v, u', v', y, z} (T.comp S) :=
  isDeterministicSuperchannel_iff.mpr
    ((isDeterministicSuperchannel_iff.mp hT).comp (isDeterministicSuperchannel_iff.mp hS))

/-- The identity higher-order map is a deterministic superchannel. -/
theorem isDeterministicSuperchannel_id :
    IsDeterministicSuperchannel.{u, v, u, v, y, z}
      (LinearMap.id : MatrixMap (a × b) (a × b)) :=
  isDeterministicSuperchannel_iff.mpr isCompletelyDeterministic_id

/-- A deterministic superchannel preserves channels on arbitrary finite
heterogeneous ancillary wire families. -/
def IsDeterministicSuperchannel.wireFamily {S : MatrixMap (a × b) (c × d)}
    (hS : IsDeterministicSuperchannel.{u, v, w, x, y, z} S) {m n : Nat}
    (R : Fin m → Type y) (T : Fin n → Type z)
    [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (N : Channel (a × (∀ i, R i)) (b × (∀ i, T i))) :
    Channel (c × (∀ i, R i)) (d × (∀ i, T i)) :=
  hS.channel N

/-- The channel with a prescribed positive semidefinite, normalized Choi
operator. -/
def channelOfChoi {J : CMatrix (a × b)} (hJpos : J.PosSemidef)
    (hJtp : partialTraceB J = 1) : Channel a b where
  map := MatrixMap.ofChoiMatrix J
  completelyPositive := MatrixMap.ofChoiMatrix_isCompletelyPositive hJpos
  tracePreserving := by
    rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi, MatrixMap.choi_ofChoiMatrix]
    exact hJtp
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _
    (MatrixMap.ofChoiMatrix_isCompletelyPositive hJpos)

/-- The channel constructed from Choi data has exactly that Choi operator. -/
@[simp] theorem choi_channelOfChoi {J : CMatrix (a × b)} (hJpos : J.PosSemidef)
    (hJtp : partialTraceB J = 1) :
    MatrixMap.choi (channelOfChoi hJpos hJtp).map = J :=
  MatrixMap.choi_ofChoiMatrix _

/-- Completion of an operation Choi operator to a channel Choi operator by an
output flag: the flagged block carries the operator, and the complementary
block carries the normalization slack, spread uniformly over the original
output system. -/
def completedChoi (J : CMatrix ((a × r) × (b × s))) :
    CMatrix ((a × r) × (b × Option s)) :=
  fun x y => match x.2.2, y.2.2 with
    | some t, some t' => J (x.1, (x.2.1, t)) (y.1, (y.2.1, t'))
    | none, none => (Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) x.1 y.1
    | _, _ => 0

omit [Fintype a] [DecidableEq b] [Fintype r] [DecidableEq s] in
/-- The flagged block of the completion is the original operator. -/
theorem completedChoi_submatrix (J : CMatrix ((a × r) × (b × s))) :
    (completedChoi J).submatrix
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s))) = J := rfl

omit [DecidableEq b] [DecidableEq s] in
set_option maxHeartbeats 1000000 in
/-- The completion of an operation Choi operator is positive semidefinite. -/
theorem completedChoi_posSemidef [Nonempty b] {J : CMatrix ((a × r) × (b × s))}
    (hJpos : J.PosSemidef) (hJle : partialTraceB J ≤ 1) :
    (completedChoi J).PosSemidef := by
  have hM : (1 - partialTraceB J).PosSemidef := Matrix.le_iff.mp hJle
  have hc : (0 : ℂ) ≤ (Fintype.card b : ℂ)⁻¹ := by positivity
  have hJe : ∀ u v : (a × r) × (b × s), star (J u v) = J v u := fun u v => by
    rw [← Matrix.conjTranspose_apply, show Matrix.conjTranspose J = J from hJpos.1]
  have hMe : ∀ u v : a × r, star ((1 - partialTraceB J) u v) = (1 - partialTraceB J) v u :=
    fun u v => by
      rw [← Matrix.conjTranspose_apply,
        show Matrix.conjTranspose (1 - partialTraceB J) = _ from hM.1]
  have hce : star ((Fintype.card b : ℂ)⁻¹) = (Fintype.card b : ℂ)⁻¹ := by
    rw [star_inv₀]
    exact congrArg _ (Complex.conj_natCast _)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · show Matrix.conjTranspose (completedChoi J) = completedChoi J
    ext x y
    rcases x with ⟨x1, x2, xo⟩
    rcases y with ⟨y1, y2, yo⟩
    rcases xo with xo | xo <;> rcases yo with yo | yo <;>
      simp only [completedChoi, Matrix.conjTranspose_apply, star_mul', star_zero,
        hJe, hMe, hce]
  · intro x
    have key : star x ⬝ᵥ (completedChoi J *ᵥ x)
        = star (fun p : (a × r) × (b × s) => x (p.1, (p.2.1, some p.2.2)))
          ⬝ᵥ (J *ᵥ (fun p : (a × r) × (b × s) => x (p.1, (p.2.1, some p.2.2)))) +
          (Fintype.card b : ℂ)⁻¹ * star (fun i : a × r => ∑ j : b, x (i, (j, none)))
            ⬝ᵥ ((1 - partialTraceB J)
              *ᵥ (fun i : a × r => ∑ j : b, x (i, (j, none)))) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
        Fintype.sum_option, completedChoi, Finset.mul_sum, zero_mul,
        zero_add, add_zero, Finset.sum_const_zero, Pi.star_apply]
      simp only [Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      have hswap1 : (∑ x_1 : a, ∑ x_2 : r, ∑ j : b, ∑ v_1 : a, ∑ v_2 : r, ∑ i : b,
              star (x ((x_1, x_2), (j, none))) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none))))
            = ∑ x_1 : a, ∑ x_2 : r, ∑ v_1 : a, ∑ j : b, ∑ v_2 : r, ∑ i : b,
              star (x ((x_1, x_2), (j, none))) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none))) :=
        Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_2 _ =>
          Finset.sum_comm
      have hswap2 : (∑ x_1 : a, ∑ x_2 : r, ∑ v_1 : a, ∑ j : b, ∑ v_2 : r, ∑ i : b,
              star (x ((x_1, x_2), (j, none))) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none))))
            = ∑ x_1 : a, ∑ x_2 : r, ∑ v_1 : a, ∑ v_2 : r, ∑ j : b, ∑ i : b,
              star (x ((x_1, x_2), (j, none))) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none))) :=
        Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_2 _ =>
          Finset.sum_congr rfl fun v_1 _ => Finset.sum_comm
      have hcoll : (∑ x_1 : a, ∑ x_2 : r, ∑ v_1 : a, ∑ v_2 : r,
              star (∑ j : b, x ((x_1, x_2), (j, none))) *
                ∑ i : b, (Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none)))
            = ∑ x_1 : a, ∑ x_2 : r, ∑ v_1 : a, ∑ v_2 : r, ∑ j : b, ∑ i : b,
              star (x ((x_1, x_2), (j, none))) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), (i, none))) :=
        Finset.sum_congr rfl fun x_1 _ => Finset.sum_congr rfl fun x_2 _ =>
          Finset.sum_congr rfl fun v_1 _ => Finset.sum_congr rfl fun v_2 _ => by
            simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_comm (f := fun i j : b =>
              star (x ((x_1, x_2), j, none)) *
                ((Fintype.card b : ℂ)⁻¹ * (1 - partialTraceB J) (x_1, x_2) (v_1, v_2) *
                  x ((v_1, v_2), i, none)))
      rw [hswap1, hswap2, ← hcoll]
      simp only [Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    rw [key]
    exact add_nonneg (hJpos.dotProduct_mulVec_nonneg _)
      (mul_nonneg hc (hM.dotProduct_mulVec_nonneg _))

omit [Fintype a] [DecidableEq b] [Fintype r] [DecidableEq s] in
/-- The output partial trace of the completion is the identity, with no
hypothesis on `J` beyond the nonempty output system: the slack block supplies
exactly the missing normalization. The total trace is correspondingly
`Fintype.card (a × r)`, not one. -/
theorem partialTraceB_completedChoi [Nonempty b] {J : CMatrix ((a × r) × (b × s))} :
    partialTraceB (completedChoi J) = 1 := by
  ext i i'
  simp only [partialTraceB, Fintype.sum_prod_type, Fintype.sum_option, completedChoi,
    Matrix.one_apply, Matrix.sub_apply, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)), one_mul,
    sub_add_cancel]

omit [DecidableEq c] [DecidableEq d] [DecidableEq r] [DecidableEq s] in
/-- Tracing out the output of a positive semidefinite matrix dominates the
trace of its flagged compression. -/
theorem partialTraceB_submatrix_le {M : CMatrix ((c × r) × (d × Option s))}
    (hM : M.PosSemidef) :
    partialTraceB (M.submatrix
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))) ≤
      partialTraceB M := by
  rw [Matrix.le_iff]
  have hnone : partialTraceB M - partialTraceB (M.submatrix
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))
        (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))) =
      partialTraceB (M.submatrix
        (Prod.map (Prod.map id id) (fun p : d × Unit => (p.1, (none : Option s))))
        (Prod.map (Prod.map id id) (fun p : d × Unit => (p.1, (none : Option s))))) := by
    ext i i'
    simp only [partialTraceB, Fintype.sum_prod_type, Fintype.sum_option,
      Matrix.submatrix_apply, Prod.map, id_eq, Prod.mk.eta, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    simp only [add_sub_cancel_right]
    simp
  rw [hnone]
  exact partialTraceB_posSemidef (hM.submatrix _)

/-- A deterministic superchannel is exactly a higher-order map that sends every
channel on every finite joint input to a completely positive, trace-preserving
operation: the stabilized form of sending channels to channels. -/
theorem isDeterministicSuperchannel_iff_channels (S : MatrixMap (a × b) (c × d)) :
    IsDeterministicSuperchannel.{u, v, w, x, y, z} S ↔
      ∀ (r : Type y) (s : Type z) [Fintype r] [DecidableEq r]
        [Fintype s] [DecidableEq s] (N : Channel (a × r) (b × s)),
        MatrixMap.IsCompletelyPositive (ancillaryAction S N.map) ∧
          MatrixMap.IsTracePreserving (ancillaryAction S N.map) := by
  constructor
  · intro h r s _ _ _ _ N
    exact ⟨(h.channel N).completelyPositive, (h.channel N).tracePreserving⟩
  · intro H
    rw [isDeterministicSuperchannel_iff]
    refine ⟨?_, ?_⟩
    · intro r s _ _ _ _ J hJ
      obtain ⟨hJpos, hJle⟩ := hJ
      rcases isEmpty_or_nonempty b with hb | hb
      · have := hb
        have hzero : ancillaryExtension S J = 0 := by
          ext p q
          have hblk : ∀ i j : r × s, (ancillaryBlock J i j : CMatrix (a × b)) = 0 :=
            fun i j => Matrix.ext fun p _ => isEmptyElim p.2
          show S (ancillaryBlock J _ _) _ _ = _
          rw [hblk]
          simp
        change (ancillaryExtension S J).PosSemidef ∧
          partialTraceB (ancillaryExtension S J) ≤ 1
        refine ⟨?_, ?_⟩
        · rw [hzero]
          exact Matrix.PosSemidef.zero
        · rw [hzero]
          have hz : partialTraceB (0 : CMatrix ((c × r) × (d × s))) = 0 := by
            ext i j
            exact Finset.sum_const_zero
          rw [hz]
          exact Matrix.PosSemidef.one.nonneg
      · have := hb
        obtain ⟨hCP, hTP⟩ :=
          H r (Option s)
            (channelOfChoi (completedChoi_posSemidef hJpos hJle)
              partialTraceB_completedChoi)
        rw [MatrixMap.IsCompletelyPositive, choi_ancillaryAction, choi_channelOfChoi] at hCP
        rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi, choi_ancillaryAction,
          choi_channelOfChoi] at hTP
        have hre : ancillaryExtension S J
            = (ancillaryExtension S (completedChoi J)).submatrix
                (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s)))
                (Prod.map (Prod.map id id) (Prod.map id (Option.some : s → Option s))) := by
          rw [← ancillaryExtension_reindex S (completedChoi J) (id : r → r)
              (Option.some : s → Option s), completedChoi_submatrix J]
        change (ancillaryExtension S J).PosSemidef ∧
          partialTraceB (ancillaryExtension S J) ≤ 1
        refine ⟨?_, ?_⟩
        · rw [hre]
          exact hCP.submatrix _
        · rw [hre, ← hTP]
          exact partialTraceB_submatrix_le hCP
    · intro r s _ _ _ _ J hJ
      obtain ⟨hJpos, hJtp⟩ := hJ
      obtain ⟨hCP, hTP⟩ := H r s (channelOfChoi hJpos hJtp)
      rw [MatrixMap.IsCompletelyPositive, choi_ancillaryAction, choi_channelOfChoi] at hCP
      rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi, choi_ancillaryAction,
        choi_channelOfChoi] at hTP
      exact ⟨hCP, hTP⟩

end
end QIT.HigherOrder
