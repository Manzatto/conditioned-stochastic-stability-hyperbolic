module
public import LeanShared.Geometry.RelativeDeterminantPerturbation

/-! A uniform normalized perturbation radius also controls the reference
determinant by the actual determinant. No norm of the reference map enters. -/
public noncomputable section
namespace LeanShared.RelativeDeterminantPerturbationLower
open scoped Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_radius (γ:ℝ) (hγ:1<γ) :
    ∃η:ℝ,0<η ∧ ∀A:E≃L[ℝ]E,∀B:E→L[ℝ]E,
      ‖A.symm.toContinuousLinearMap.comp (B-A.toContinuousLinearMap)‖≤η →
      |A.toContinuousLinearMap.det| ≤ γ*|B.det| := by
  have atIdentity : 1<γ*|(ContinuousLinearMap.id ℝ E).det| := by
    change 1<γ*|(LinearMap.id:E→ₗ[ℝ]E).det|
    simpa only [LinearMap.det_id,abs_one,mul_one] using hγ
  have limit := ((continuous_const.mul ContinuousLinearMap.continuous_det.abs).continuousAt
    (x:=ContinuousLinearMap.id ℝ E)).eventually (lt_mem_nhds atIdentity)
  obtain ⟨ε,positive,nearby⟩ := Metric.eventually_nhds_iff.mp limit
  refine ⟨ε/2,half_pos positive,fun A B small=>?_⟩
  let D := A.symm.toContinuousLinearMap.comp (B-A.toContinuousLinearMap)
  have distance : dist (ContinuousLinearMap.id ℝ E+D) (ContinuousLinearMap.id ℝ E)<ε := by
    rw [dist_eq_norm,add_sub_cancel_left]
    exact small.trans_lt (half_lt_self positive)
  have determinant := (nearby distance).le
  have factor : B=A.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E+D) := by
    ext x
    change B x=A (x+A.symm (B x-A x))
    rw [map_add,A.apply_symm_apply]
    abel
  have absolute : |B.det| = |A.toContinuousLinearMap.det| * |(ContinuousLinearMap.id ℝ E+D).det| := by
    conv_lhs => rw [factor]
    simp only [ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp,abs_mul]
  calc
    |A.toContinuousLinearMap.det| = |A.toContinuousLinearMap.det| * 1 := (mul_one _).symm
    _ ≤ |A.toContinuousLinearMap.det| * (γ*|(ContinuousLinearMap.id ℝ E+D).det|) :=
      mul_le_mul_of_nonneg_left determinant (abs_nonneg _)
    _ = γ*|B.det| := by rw [absolute]; ring
end LeanShared.RelativeDeterminantPerturbationLower
