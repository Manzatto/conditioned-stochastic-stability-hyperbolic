module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A single normalized perturbation radius controls relative determinants
for every invertible linear map, independently of its norm. -/
public noncomputable section
namespace LeanShared.RelativeDeterminantPerturbation
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ A : E ≃L[ℝ] E, ∀ B : E →L[ℝ] E,
      ‖A.symm.toContinuousLinearMap.comp (B - A.toContinuousLinearMap)‖ ≤ η →
      |B.det| ≤ γ * |A.toContinuousLinearMap.det| := by
  have atIdentity : |(ContinuousLinearMap.id ℝ E).det| < γ := by
    change |(LinearMap.id : E →ₗ[ℝ] E).det| < γ
    simpa only [LinearMap.det_id, abs_one] using hγ
  have limit := (ContinuousLinearMap.continuous_det.abs.continuousAt
    (x := ContinuousLinearMap.id ℝ E)).eventually (gt_mem_nhds atIdentity)
  obtain ⟨ε, hε, nearby⟩ := Metric.eventually_nhds_iff.mp limit
  refine ⟨ε / 2, half_pos hε, fun A B small => ?_⟩
  let D := A.symm.toContinuousLinearMap.comp (B - A.toContinuousLinearMap)
  have distance : dist (ContinuousLinearMap.id ℝ E + D) (ContinuousLinearMap.id ℝ E) < ε := by
    rw [dist_eq_norm, add_sub_cancel_left]
    exact small.trans_lt (half_lt_self hε)
  have determinant := (nearby distance).le
  have factor : B = A.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E + D) := by
    ext x
    change B x = A (x + A.symm (B x - A x))
    rw [map_add, A.apply_symm_apply]
    abel
  calc
    |B.det| = |A.toContinuousLinearMap.det| * |(ContinuousLinearMap.id ℝ E + D).det| := by
      conv_lhs => rw [factor]
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.det_comp, abs_mul]
    _ ≤ |A.toContinuousLinearMap.det| * γ := mul_le_mul_of_nonneg_left determinant (abs_nonneg _)
    _ = _ := mul_comm _ _

end LeanShared.RelativeDeterminantPerturbation
