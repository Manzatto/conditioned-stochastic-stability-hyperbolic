module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic.Linarith

/-! Quantitative inverse error for an actual equivalence close to the
identity. This turns the nearby-reference projection error into the error
of the inverse coordinate change used in a centered nonlinear map. -/
public noncomputable section
namespace LeanShared.NearIdentityEquivalenceBounds

 theorem inverse_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E ≃L[ℝ] E) (δ : ℝ) (small : δ < 1)
    (bound : ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ ≤ δ) :
    ‖R.symm.toContinuousLinearMap‖ ≤ 1 / (1 - δ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖R.symm v‖ ≤ (1 / (1 - δ)) * ‖v‖
  have error := (R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E).le_opNorm (R.symm v)
  change ‖R (R.symm v) - R.symm v‖ ≤
    ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ * ‖R.symm v‖ at error
  rw [R.apply_symm_apply] at error
  have triangle := norm_add_le v (R.symm v - v)
  rw [add_sub_cancel] at triangle
  have scaled := mul_le_mul_of_nonneg_right bound (norm_nonneg (R.symm v))
  rw [norm_sub_rev] at error
  have lower : ‖R.symm v‖ * (1 - δ) ≤ ‖v‖ := by nlinarith
  have result := (le_div_iff₀ (sub_pos.mpr small)).2 lower
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm] using result

 theorem inverse_sub_id_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : E ≃L[ℝ] E) (δ : ℝ) (small : δ < 1)
    (bound : ‖R.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ ≤ δ) :
    ‖R.symm.toContinuousLinearMap - ContinuousLinearMap.id ℝ E‖ ≤ δ / (1 - δ) := by
  have nonnegative : 0 ≤ δ := (norm_nonneg _).trans bound
  have identity : R.symm.toContinuousLinearMap - ContinuousLinearMap.id ℝ E =
      (ContinuousLinearMap.id ℝ E - R.toContinuousLinearMap).comp R.symm.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    change R.symm v - v = R.symm v - R (R.symm v)
    rw [R.apply_symm_apply]
  rw [identity]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ E - R.toContinuousLinearMap‖ * ‖R.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ δ * (1 / (1 - δ)) := by
      apply mul_le_mul
      · simpa only [norm_sub_rev] using bound
      · exact inverse_norm_le R δ small bound
      · exact norm_nonneg R.symm.toContinuousLinearMap
      · exact nonnegative
    _ = _ := by rw [mul_one_div]

end LeanShared.NearIdentityEquivalenceBounds
