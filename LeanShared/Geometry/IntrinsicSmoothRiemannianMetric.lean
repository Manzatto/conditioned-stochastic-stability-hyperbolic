module
public import LeanShared.Geometry.FrameRiemannianMetric
public import LeanShared.Geometry.SmoothImmersionRiemannianMetric
public import LeanShared.Geometry.SmoothMetricBundleClasses

/-! Every compact smooth finite-dimensional Hilbert-model manifold
internally supplies a genuine smooth Riemannian metric. Pointwise chart
frames supply only an auxiliary topology-compatible raw metric; no global
continuous trivialization or product metric is assumed. -/
@[expose] public noncomputable section
open Bundle IsManifold
open scoped Manifold ContDiff Bundle
namespace LeanShared.IntrinsicSmoothRiemannianMetric
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- Actual pointwise inverse chart trivialization, without a continuity
assertion as the basepoint varies. -/
def pointwiseFrame (x : M) : E ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x :=
  ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)).symm

/-- The auxiliary raw metric preserves the original fiber topology. -/
def rawMetric : RiemannianMetric (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
  FrameRiemannianMetric.metric (F := E) (pointwiseFrame (E := E) (M := M))

variable [T2Space M] [CompactSpace M]

/-- A genuine C-infinity metric, requiring no original Riemannian bundle. -/
def smoothMetric : ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E
    (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
  letI : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) := ⟨rawMetric (E := E) (M := M)⟩
  CanonicalSmoothReferenceMetric.smoothMetric (E := E) (M := M)

theorem continuous_bundle :
    letI : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
      ⟨(smoothMetric (E := E) (M := M)).toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
  SmoothMetricBundleClasses.continuous _

theorem smooth_bundle :
    letI : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
      ⟨(smoothMetric (E := E) (M := M)).toRiemannianMetric⟩
    IsContMDiffRiemannianBundle (𝓘(ℝ, E)) ∞ E (TangentSpace (𝓘(ℝ, E)) (M := M)) :=
  SmoothMetricBundleClasses.smooth _

end LeanShared.IntrinsicSmoothRiemannianMetric
