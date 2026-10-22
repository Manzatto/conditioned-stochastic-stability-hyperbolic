module
public import LeanShared.Geometry.BoundedRiemannianInverseChartLipschitz
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Tactic.Ring

/-! A native Holder bound gives the literal two-point fractional chart
regularity, by the proved inverse-chart length estimate. -/
public noncomputable section
namespace LeanShared.BoundedRiemannianMetric
open Set Manifold Metric Bundle
open scoped Topology Manifold ContDiff Bundle NNReal

set_option maxHeartbeats 1600000 in
theorem regular_of_native_holder
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [T3Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) 1 M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {f : M → F} (continuous : Continuous f)
    {C : ℝ} (hC : 0 ≤ C)
    (holder : let _ : MetricSpace M := metric (E := E)
      ∀ x y, ‖f x-f y‖ ≤ C*dist x y^a) :
    FractionalManifoldRegularity.Regular (E := E) (F := F) a f := by
  let _ : MetricSpace M := metric (E := E)
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  refine ⟨ha.le,?_,?_⟩
  · rw [floor]
    exact contMDiff_zero_iff.mpr continuous
  · intro _ x
    let e := extChartAt (𝓘(ℝ,E)) x
    obtain ⟨r,hr,L,_,safe,lip⟩ := inverse_chart_local_lipschitz (E := E) x
    refine ⟨ball (e x) r,isOpen_ball,mem_ball_self hr,?_,C*(L:ℝ)^a,
      mul_nonneg hC (Real.rpow_nonneg L.coe_nonneg _),?_⟩
    · intro y hy
      exact ⟨safe hy,by simp [chartAt_self_eq]⟩
    · intro y hy z hz
      have power := Real.rpow_le_rpow dist_nonneg (lip y hy z hz) ha.le
      rw [Real.mul_rpow L.coe_nonneg dist_nonneg] at power
      have actual := (holder (e.symm y) (e.symm z)).trans
        (mul_le_mul_of_nonneg_left power hC)
      have estimate : ‖f (e.symm y)-f (e.symm z)‖ ≤ (C*(L:ℝ)^a)*‖y-z‖^a := by
        simpa only [dist_eq_norm,mul_assoc] using actual
      rw [floor]
      simpa only [Nat.cast_zero,sub_zero,iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        ←map_sub,LinearIsometryEquiv.norm_map,FractionalManifoldRegularity.chartMap,
        extChartAt_model_space_eq_id,PartialEquiv.refl_coe,id_eq] using estimate

end LeanShared.BoundedRiemannianMetric
