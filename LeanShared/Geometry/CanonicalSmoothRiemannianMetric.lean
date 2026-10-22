module
public import LeanShared.Geometry.CanonicalSmoothReferenceMetric
public import LeanShared.Geometry.SmoothImmersionGramMetric

/-! A genuine smooth positive reference Riemannian metric is constructed
from the internally produced Whitney immersion. It is separate from the
supplied continuous metric used for hyperbolicity. -/
public noncomputable section
namespace LeanShared.CanonicalSmoothReferenceMetric
open Bundle Manifold Set
open scoped Topology Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

/-- The smooth reference is produced, not assumed. -/
@[expose] def smoothMetric :
    ContMDiffRiemannianMetric (𝓘(ℝ,E)) ∞ E (fun x : M => TangentSpace (𝓘(ℝ,E)) x) :=
  SmoothImmersionReferenceMetric.smoothPullbackMetric
    (canonicalData (E := E) (M := M)).map
    (canonicalData (E := E) (M := M)).smooth
    (canonicalData (E := E) (M := M)).injective

/-- Installing only the constructed reference metric gives the full smooth
metric class. No regularity of the supplied original metric is strengthened. -/
theorem smooth_reference :
    let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) :=
      ⟨(smoothMetric (E := E) (M := M)).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle (𝓘(ℝ,E)) ∞ E (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := by
  infer_instance

/-- The same produced reference has the continuous metric class needed for
native norm and length estimates. -/
theorem continuous_reference :
    let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) :=
      ⟨(smoothMetric (E := E) (M := M)).toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := by
  let g := smoothMetric (E := E) (M := M)
  let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x) := ⟨g.toRiemannianMetric⟩
  change IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  exact ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩

end LeanShared.CanonicalSmoothReferenceMetric
