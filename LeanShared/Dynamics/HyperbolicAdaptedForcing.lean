module
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
public import LeanShared.Topology.CompactNearDiagonalContinuity
import all LeanShared.Geometry.CompactUniformCenteredCharts
import Mathlib.Tactic.FieldSimp

/-! The actual centered one-step map has arbitrarily small origin forcing
at sufficiently close reference pairs. The radius may be fixed beforehand. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet CenteredManifoldCoordinates
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.forcing_window {system : PatchSystem b} (atlas : ChartAtlas system)
    (τ : ℝ) (positiveτ : 0 < τ) :
    ∃ η > 0, ∀ c ∈ atlas.centers, ∀ d ∈ atlas.centers,
      ∀ x (hx : x ∈ atlas.patch c), ∀ y (hy : y ∈ atlas.patch d),
      dist (T x.val) y.val < η →
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.referenceFrame c ⟨x, atlas.inside c hx⟩)
      let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
        (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
      T x.val ∈ (chartAt E d.val).source ∧
      ‖centered L R ((chartAt E c.val) x.val) ((chartAt E d.val) y.val)
        (chartAt E d.val ∘ T ∘ (chartAt E c.val).symm) 0‖ < τ := by
  have positiveB : 0 < atlas.bound := lt_of_lt_of_le zero_lt_one atlas.one_le_bound
  let K (c : Λ) := Subtype.val '' atlas.patch c
  have compactK (c : Λ) : IsCompact (K c) := (atlas.compact c).image continuous_subtype_val
  have sourceK (c : Λ) : K c ⊆ (chartAt E c.val).source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (atlas.inside c hx).2
  have windows (c : Λ) := CompactNearDiagonalContinuity.exists_radius (K c)
    (chartAt E c.val).source (compactK c) (chartAt E c.val).open_source (sourceK c)
    (chartAt E c.val) (chartAt E c.val).continuousOn (τ / atlas.bound)
    (div_pos positiveτ positiveB)
  choose radii positiveRadii estimates using windows
  obtain ⟨η, positiveη, common⟩ := CompactUniformCenteredCharts.common_positive atlas.centers radii
    (fun c _ => positiveRadii c)
  refine ⟨η, positiveη, ?_⟩
  intro c _hc d hd x hx y hy near
  have data := estimates d y.val ⟨y, hy, rfl⟩ (T x.val)
    (by simpa only [dist_comm] using near.trans_le (common d hd))
  refine ⟨data.1, ?_⟩
  let R := ContinuousCenteredFrameCharts.chartFrame d.val y.val (atlas.inside d hy).2
    (system.referenceFrame d ⟨y, atlas.inside d hy⟩)
  have difference : ‖(chartAt E d.val) (T x.val) - (chartAt E d.val) y.val‖ < τ / atlas.bound := by
    simpa only [dist_eq_norm, norm_sub_rev] using data.2
  have estimate := (R.symm.toContinuousLinearMap.le_opNorm
    ((chartAt E d.val) (T x.val) - (chartAt E d.val) y.val)).trans
    (mul_le_mul_of_nonneg_right (atlas.frame_bounds d hd y hy).2 (norm_nonneg _))
  have cancellation : atlas.bound * (τ / atlas.bound) = τ := by field_simp
  have strict := mul_lt_mul_of_pos_left difference positiveB
  rw [cancellation] at strict
  simp only [centered, _root_.map_zero, add_zero, Function.comp_apply,
    (chartAt E c.val).left_inv (atlas.inside c hx).2]
  exact (show ‖R.symm ((chartAt E d.val) (T x.val) - (chartAt E d.val) y.val)‖ ≤
    atlas.bound * ‖(chartAt E d.val) (T x.val) - (chartAt E d.val) y.val‖ from estimate).trans_lt strict

end LeanShared.HyperbolicAdaptedPatchSystem
