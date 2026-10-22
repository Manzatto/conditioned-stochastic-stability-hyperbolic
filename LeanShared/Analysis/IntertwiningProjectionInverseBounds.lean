module
public import LeanShared.Analysis.IntertwiningProjectionTransport
public import Mathlib.Tactic.FieldSimp

/-! Quantitative inverse bounds for the actual simultaneous transport of the
stable and unstable projections. These estimates control the inverse block
when a pseudo-orbit reference target differs from the exact image. -/
public noncomputable section
namespace LeanShared.IntertwiningProjectionTransport

private theorem lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v) (v : E) :
    (1 - ‖P - Q‖ * (2 * ‖P‖ + 1)) * ‖v‖ ≤ ‖transport P Q v‖ := by
  have error := (transport P Q - ContinuousLinearMap.id ℝ E).le_opNorm v
  have bound := mul_le_mul_of_nonneg_right (norm_sub_id_le P Q idempotentP) (norm_nonneg v)
  have triangle := norm_add_le (transport P Q v) (v - transport P Q v)
  rw [add_sub_cancel] at triangle
  change ‖transport P Q v - v‖ ≤
    ‖transport P Q - ContinuousLinearMap.id ℝ E‖ * ‖v‖ at error
  rw [norm_sub_rev] at error
  nlinarith

theorem inverse_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1) :
    ‖(equivalence P Q idempotentP small).symm.toContinuousLinearMap‖ ≤
      1 / (1 - ‖P - Q‖ * (2 * ‖P‖ + 1)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(equivalence P Q idempotentP small).symm v‖ ≤
    (1 / (1 - ‖P - Q‖ * (2 * ‖P‖ + 1))) * ‖v‖
  have lower := lower_bound P Q idempotentP ((equivalence P Q idempotentP small).symm v)
  rw [← equivalence_apply P Q idempotentP small,
    ContinuousLinearEquiv.apply_symm_apply] at lower
  have positive : 0 < 1 - ‖P - Q‖ * (2 * ‖P‖ + 1) := sub_pos.mpr small
  have result : ‖(equivalence P Q idempotentP small).symm v‖ ≤
      ‖v‖ / (1 - ‖P - Q‖ * (2 * ‖P‖ + 1)) :=
    (le_div_iff₀ positive).2 (by nlinarith only [lower])
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using result

theorem inverse_sub_id_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P Q : E →L[ℝ] E) (idempotentP : ∀ v, P (P v) = P v)
    (small : ‖P - Q‖ * (2 * ‖P‖ + 1) < 1) :
    ‖(equivalence P Q idempotentP small).symm.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ E‖ ≤
      (‖P - Q‖ * (2 * ‖P‖ + 1)) /
        (1 - ‖P - Q‖ * (2 * ‖P‖ + 1)) := by
  have identity : (equivalence P Q idempotentP small).symm.toContinuousLinearMap -
      ContinuousLinearMap.id ℝ E =
      (ContinuousLinearMap.id ℝ E - transport P Q).comp
        (equivalence P Q idempotentP small).symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    change (equivalence P Q idempotentP small).symm v - v =
      (equivalence P Q idempotentP small).symm v -
        transport P Q ((equivalence P Q idempotentP small).symm v)
    rw [← equivalence_apply P Q idempotentP small, ContinuousLinearEquiv.apply_symm_apply]
  rw [identity]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ E - transport P Q‖ *
        ‖(equivalence P Q idempotentP small).symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖P - Q‖ * (2 * ‖P‖ + 1)) *
        (1 / (1 - ‖P - Q‖ * (2 * ‖P‖ + 1))) := by
      apply mul_le_mul
      · rw [norm_sub_rev]
        exact norm_sub_id_le P Q idempotentP
      · exact inverse_norm_le P Q idempotentP small
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [mul_one_div]

end LeanShared.IntertwiningProjectionTransport
