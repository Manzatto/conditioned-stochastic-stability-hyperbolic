module
public import LeanShared.Geometry.BoundedRiemannianSmoothHolderCore
public import LeanShared.Geometry.SmoothHolderTestSpaces

/-! The canonical full little Holder tests for the constructed native
length metric, sealed separately from the original noise metric. -/
@[expose] public noncomputable section
namespace LeanShared.NativeFullHolderTests
open Set Bundle
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (b : ℝ) (hb1 : b ≤ 1)

abbrev Full :=
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  ↥(SmoothHolderTestSpaces.space (E := E) (M := M) b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ)

instance full_complete : CompleteSpace (Full (E := E) (M := M) b hb1) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact SmoothHolderTestSpaces.space_complete b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ

def view : Full (E := E) (M := M) b hb1 →ₗ[ℂ] (M → ℂ) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact SmoothHolderTestSpaces.view (E := E) (M := M) b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ

def core : SmoothSupportedManifoldCore.core (E := E) (univ : Set M) →ₗ[ℂ]
    Full (E := E) (M := M) b hb1 := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact SmoothHolderTestSpaces.coreMap (E := E) (M := M) b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ

theorem view_injective : Function.Injective (view (E := E) (M := M) b hb1) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  intro v w equality
  apply SmoothHolderTestSpaces.physical_injective b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ
  ext x
  exact congrFun equality x

theorem view_core (c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M)) (x : M) :
    view b hb1 (core b hb1 c) x = c.val x := rfl

end LeanShared.NativeFullHolderTests
