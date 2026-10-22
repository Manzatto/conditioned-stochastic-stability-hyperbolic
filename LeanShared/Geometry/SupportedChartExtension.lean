module
public import LeanShared.Geometry.ChartLocalization
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! Literal inverse-chart extension by zero. Compact support inside the
chart target proves continuity across its boundary and gives exact
support transport. This is the actual chart-patching map, not a supplied
global realization. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.SupportedChartExtension
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  (e : OpenPartialHomeomorph M E)

@[expose] def function (h : E → ℂ) (x : M) : ℂ := by
  classical
  exact if x ∈ e.source then h (e x) else 0

omit [NormedSpace ℝ E] [ChartedSpace E M] [T2Space M] in
theorem zero_outside (h : E → ℂ) (_support : tsupport h ⊆ e.target)
    (x : M) (hx : x ∉ e.symm '' tsupport h) : function e h x = 0 := by
  by_cases source : x ∈ e.source
  · have zero : h (e x) = 0 := by
      by_contra hn
      apply hx
      exact ⟨e x, subset_tsupport h hn, e.left_inv source⟩
    simp only [function, ite_eq_left source, zero]
  · exact ite_eq_right source

omit [NormedSpace ℝ E] [ChartedSpace E M] [T2Space M] in
theorem compact_image {h : E → ℂ} (compact : HasCompactSupport h)
    (support : tsupport h ⊆ e.target) : IsCompact (e.symm '' tsupport h) :=
  compact.image_of_continuousOn (e.symm.continuousOn.mono support)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem support_subset {h : E → ℂ} (compact : HasCompactSupport h)
    (support : tsupport h ⊆ e.target) : tsupport (function e h) ⊆ e.symm '' tsupport h := by
  apply closure_minimal _ (compact_image e compact support).isClosed
  intro x hx
  by_contra hn
  exact hx (zero_outside e h support x hn)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem continuous {h : E → ℂ} (continuous : Continuous h)
    (compact : HasCompactSupport h) (support : tsupport h ⊆ e.target) :
    Continuous (function e h) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases source : x ∈ e.source
  · apply (continuous.continuousAt.comp
      (e.continuousOn.continuousAt (e.open_source.mem_nhds source))).congr
    filter_upwards [e.open_source.mem_nhds source] with y hy
    exact (ite_eq_left hy).symm
  · have outside : x ∉ e.symm '' tsupport h := by
      rintro ⟨y, hy, rfl⟩
      exact source (e.map_target (support hy))
    apply continuousAt_const.congr
    filter_upwards [(compact_image e compact support).isClosed.isOpen_compl.mem_nhds outside]
      with y hy
    exact (zero_outside e h support y hy).symm

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem compact_support {h : E → ℂ} (compact : HasCompactSupport h)
    (support : tsupport h ⊆ e.target) : HasCompactSupport (function e h) :=
  (compact_image e compact support).of_isClosed_subset (isClosed_tsupport _)
    (support_subset e compact support)

omit [NormedSpace ℝ E] [ChartedSpace E M] [T2Space M] in
theorem coordinate {h : E → ℂ} (y : E) (hy : y ∈ e.target) :
    function e h (e.symm y) = h y := by
  simp only [function, ite_eq_left (e.map_target hy), e.right_inv hy]

variable (he : e ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)

include he in
theorem smooth {h : E → ℂ} (smooth : ContDiff ℝ ∞ h)
    (compact : HasCompactSupport h) (support : tsupport h ⊆ e.target) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (function e h) := by
  intro x
  by_cases source : x ∈ e.source
  · apply ((smooth.contMDiff (e x)).comp x
      (contMDiffAt_of_mem_maximalAtlas he source)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds source] with y hy
    exact ite_eq_left hy
  · have outside : x ∉ e.symm '' tsupport h := by
      rintro ⟨y, hy, rfl⟩
      exact source (e.map_target (support hy))
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [(compact_image e compact support).isClosed.isOpen_compl.mem_nhds outside]
      with y hy
    exact zero_outside e h support y hy
end LeanShared.SupportedChartExtension
