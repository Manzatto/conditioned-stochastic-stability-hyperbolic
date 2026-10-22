module
public import LeanShared.Geometry.SupportedChartExtension
public import LeanShared.Geometry.AtlasHolderRegularity
public import LeanShared.Geometry.BoundedHolderSpace

/-! Actual Hölder graph vectors, supported strictly inside a genuine
chart, extend to globally fractional-regular manifold functions. Chart
changes and the zero extension are proved; no quantitative assertion
about an arbitrary global metric is used. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.SupportedChartExtension
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (v : BoundedHolderSpace.graph E a)

include he ha ha1 in
theorem graph_regular (compact : HasCompactSupport (fun y => BoundedHolderSpace.physical E a v y))
    (support : tsupport (fun y => BoundedHolderSpace.physical E a v y) ⊆ e.target) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
      (function e (fun y => BoundedHolderSpace.physical E a v y)) := by
  let h : E → ℂ := fun y => BoundedHolderSpace.physical E a v y
  apply FractionalManifoldRegularity.regular_of_atlas_holder ha ha1
    (continuous e (BoundedHolderSpace.physical E a v).continuous compact support)
  intro x
  by_cases source : x ∈ e.source
  · refine ⟨e, he, source, e.target, e.open_target.mem_nhds (e.map_source source),
      subset_rfl, ‖v‖, norm_nonneg _, ?_⟩
    intro y hy z hz
    rw [coordinate e y hy, coordinate e z hz]
    simpa only [dist_eq_norm] using BoundedHolderSpace.increment_bound E a v y z
  · have outside : x ∉ e.symm '' tsupport h := by
      rintro ⟨y, hy, rfl⟩
      exact source (e.map_target (support hy))
    let O := (e.symm '' tsupport h)ᶜ
    have openO : IsOpen O := (compact_image e compact support).isClosed.isOpen_compl
    let c := chartAt E x
    let D := c.target ∩ c.symm ⁻¹' O
    have target : c.target ∈ 𝓝 (c x) := c.open_target.mem_nhds (c.map_source (mem_chart_source E x))
    have nearO : c.symm ⁻¹' O ∈ 𝓝 (c x) :=
      (c.symm.continuousAt (c.map_source (mem_chart_source E x))).preimage_mem_nhds
        (by simpa only [c.left_inv (mem_chart_source E x)] using openO.mem_nhds outside)
    refine ⟨c, chart_mem_maximalAtlas x, mem_chart_source E x, D,
      inter_mem target nearO, inter_subset_left, 0, le_rfl, ?_⟩
    intro y hy z hz
    rw [zero_outside e h support _ hy.2, zero_outside e h support _ hz.2]
    simp only [sub_self, norm_zero, zero_mul, le_refl]
end LeanShared.SupportedChartExtension
