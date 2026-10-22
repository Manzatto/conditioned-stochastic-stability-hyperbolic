module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

/-! Actual near-identity transport intertwining two nearby projections.
It applies in one coordinate space and requires no continuous choice of
frames or global trivialization of their ranges. -/
public noncomputable section
namespace LeanShared.IntertwiningProjectionTransport

@[expose] def transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) : E →L[ℝ] E :=
  Q.comp P + (ContinuousLinearMap.id ℝ E - Q).comp (ContinuousLinearMap.id ℝ E - P)

theorem commutes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (idempotentQ : ∀ v, Q (Q v) = Q v) :
    Q.comp (transport P Q) = (transport P Q).comp P := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [transport,ContinuousLinearMap.comp_apply,add_apply,
    sub_apply,ContinuousLinearMap.id_apply,map_add,map_sub,idempotentP,idempotentQ,
    sub_self,map_zero,add_zero]

theorem sub_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v) :
    transport P Q - ContinuousLinearMap.id ℝ E =
      (Q - P).comp (P + P - ContinuousLinearMap.id ℝ E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [transport,ContinuousLinearMap.comp_apply,add_apply,
    sub_apply,ContinuousLinearMap.id_apply,map_add,map_sub,idempotentP]
  abel

theorem norm_sub_id_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v) :
    ‖transport P Q - ContinuousLinearMap.id ℝ E‖ ≤ ‖P - Q‖ * (2 * ‖P‖ + 1) := by
  rw [sub_id P Q idempotentP]
  have factor : ‖P + P - ContinuousLinearMap.id ℝ E‖ ≤ 2 * ‖P‖ + 1 :=
    (norm_sub_le _ _).trans (by nlinarith [norm_add_le P P, ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)])
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    rw [norm_sub_rev Q P]
    exact mul_le_mul_of_nonneg_left factor (norm_nonneg _))

theorem norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v) :
    ‖transport P Q‖ ≤ 1 + ‖P - Q‖ * (2 * ‖P‖ + 1) := by
  have triangle := norm_add_le (transport P Q - ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  rw [sub_add_cancel] at triangle
  nlinarith [norm_sub_id_le P Q idempotentP, ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)]

theorem isUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1) : IsUnit (transport P Q) := by
  have close : ‖1 - transport P Q‖ < 1 := by
    change ‖ContinuousLinearMap.id ℝ E - transport P Q‖ < 1
    rw [norm_sub_rev]
    exact (norm_sub_id_le P Q idempotentP).trans_lt small
  have invertible := isUnit_one_sub_of_norm_lt_one close
  simpa only [sub_sub_cancel] using invertible

@[expose] def equivalence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (transport P Q)
    (LinearMap.ker_eq_bot.mpr ((ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit P Q idempotentP small)).1))
    (LinearMap.range_eq_top.mpr ((ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit P Q idempotentP small)).2))

theorem equivalence_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1) (v : E) :
    equivalence P Q idempotentP small v = transport P Q v := rfl

end LeanShared.IntertwiningProjectionTransport
