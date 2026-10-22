module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Topology.Algebra.Support

/-! Genuine smooth vector-valued chart extensions by zero. Compact support
inside the chart target proves smoothness across the chart boundary. -/
public noncomputable section
namespace LeanShared.SupportedVectorChartExtension
open Set IsManifold
open scoped Topology Manifold ContDiff

@[expose] def function
    {E F M : Type*} [TopologicalSpace E] [TopologicalSpace M] [Zero F]
    (e : OpenPartialHomeomorph M E) (h : E → F) (x : M) : F := by
  classical
  exact if x ∈ e.source then h (e x) else 0

theorem smooth
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (h : E → F) (regular : ContDiff ℝ ∞ h) (compact : HasCompactSupport h)
    (support : tsupport h ⊆ e.target) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) ∞ (function e h) := by
  classical
  have compactK : IsCompact (e.symm '' tsupport h) :=
    compact.isCompact.image_of_continuousOn (e.symm.continuousOn.mono support)
  intro x
  by_cases source : x ∈ e.source
  · apply ((regular.contMDiff (e x)).comp x
      (contMDiffAt_of_mem_maximalAtlas he source)).congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds source] with y hy
    exact ite_eq_left hy
  · have outside : x ∉ e.symm '' tsupport h := by
      rintro ⟨y,hy,rfl⟩
      exact source (e.map_target (support hy))
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [compactK.isClosed.isOpen_compl.mem_nhds outside] with y hy
    by_cases inside : y ∈ e.source
    · have vanish : h (e y) = 0 := by
        by_contra nonzero
        exact hy ⟨e y,subset_tsupport h nonzero,e.left_inv inside⟩
      change (if y ∈ e.source then h (e y) else 0) = 0
      rw [ite_eq_left inside,vanish]
    · exact ite_eq_right inside

end LeanShared.SupportedVectorChartExtension
