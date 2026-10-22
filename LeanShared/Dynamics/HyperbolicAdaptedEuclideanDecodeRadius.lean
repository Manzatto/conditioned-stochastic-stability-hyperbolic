module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanFrameBounds
public import LeanShared.Geometry.CompactNormalizedDecodeRadius
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import LeanShared.Dynamics.HyperbolicAdaptedChartAtlas
import Mathlib.Tactic.Linarith

/-! Common actual chart-frame bounds in the same Euclidean adapted model. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem ChartAtlas.euclidean_decode_radius {system : PatchSystem b} (atlas : ChartAtlas system)
    (η : ℝ) (positiveη : 0 < η) :
    ∃ radius > 0, ∀ c ∈ atlas.centers, ∀ x (hx : x ∈ atlas.patch c),
      let L := ContinuousCenteredFrameCharts.chartFrame c.val x.val (atlas.inside c hx).2
        (system.euclideanReferenceFrame c ⟨x,atlas.inside c hx⟩)
      ∀ z, ‖z‖ ≤ radius → (chartAt E c.val) x.val+L z ∈ (chartAt E c.val).target ∧
        dist ((chartAt E c.val).symm ((chartAt E c.val) x.val+L z)) x.val < η := by
  let ambient (c : Λ) : Set M := Subtype.val '' atlas.patch c
  have compactAmbient (c : Λ) : IsCompact (ambient c) := (atlas.compact c).image continuous_subtype_val
  have ambientInside (c : Λ) : ambient c ⊆ (chartAt E c.val).source := by
    rintro _ ⟨x,hx,rfl⟩
    exact (atlas.inside c hx).2
  have windows (c : Λ) := CompactNormalizedDecodeRadius.exists_radius (P := system.EuclideanModel)
    (chartAt E c.val) (ambient c) (compactAmbient c) (ambientInside c) (2*atlas.bound)
    (by linarith [atlas.one_le_bound]) η positiveη
  choose radii positiveRadii bounds using windows
  obtain ⟨radius,positiveRadius,common⟩ := CompactUniformCenteredCharts.common_positive atlas.centers radii
    (fun c _ => positiveRadii c)
  refine ⟨radius,positiveRadius,?_⟩
  intro c hc x hx
  dsimp only
  intro z small
  exact bounds c x.val ⟨x,hx,rfl⟩ _ (atlas.euclidean_frame_bounds c hc x hx).1 z
    (small.trans (common c hc))

end LeanShared.HyperbolicAdaptedPatchSystem
