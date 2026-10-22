module
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! Explicit proved continuity and smoothness classes for a constructed
smooth metric. These avoid dependent instance search selecting an earlier
fiber norm while changing only the Riemannian bundle structure. -/
@[expose] public noncomputable section
open Bundle IsManifold
open scoped Manifold ContDiff Bundle
namespace LeanShared.SmoothMetricBundleClasses
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- The actual bilinear section of the constructed smooth metric is
continuous in the same original tangent bundle topology. -/
theorem continuous (g : ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E
    (TangentSpace (𝓘(ℝ, E)) (M := M))) :
    letI : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) := ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) (M := M)) := by
  let : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) := ⟨g.toRiemannianMetric⟩
  exact ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩

/-- The actual metric has the genuine C-infinity Riemannian bundle class. -/
theorem smooth (g : ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E
    (TangentSpace (𝓘(ℝ, E)) (M := M))) :
    letI : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle (𝓘(ℝ, E)) ∞ E (TangentSpace (𝓘(ℝ, E)) (M := M)) := by
  let : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) := ⟨g.toRiemannianMetric⟩
  exact ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩

end LeanShared.SmoothMetricBundleClasses
