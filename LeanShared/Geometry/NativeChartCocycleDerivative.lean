module

public import LeanShared.Geometry.TangentChartUniformBounds
public import LeanShared.Geometry.BundleProjectionCocycleCoordinates

/-! The actual derivative of a fixed-chart coordinate map is exactly the
native tangent-bundle coordinate cocycle. The source and target charts
are independent, and no derivative-identification premise is assumed. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.NativeChartCocycleDerivative
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

theorem fderiv_eq (f : M → M) (differentiable : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f)
    (source target x : M) (hx : x ∈ (chartAt E source).source)
    (hy : f x ∈ (chartAt E target).source) :
    fderiv ℝ ((chartAt E target) ∘ f ∘ (chartAt E source).symm) ((chartAt E source) x) =
      BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) source)
        (trivializationAt E (TangentSpace (𝓘(ℝ,E))) target) x (f x)
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) := by
  let c := chartAt E source
  let d := chartAt E target
  let C := (CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas source)).mfderiv hx
  let D := (CompactRiemannianChartBounds.chart_differentiable d (chart_mem_maximalAtlas target)).mfderiv hy
  have first : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c.symm (c x) C.symm.toContinuousLinearMap :=
    ((CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas source)).mdifferentiableAt_symm
      (c.map_source hx)).hasMFDerivAt
  have middle : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f (c.symm (c x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) := by
    rw [c.left_inv hx]
    exact (differentiable x).hasMFDerivAt
  have last : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) d (f (c.symm (c x))) D.toContinuousLinearMap := by
    rw [c.left_inv hx]
    exact ((CompactRiemannianChartBounds.chart_differentiable d
      (chart_mem_maximalAtlas target)).mdifferentiableAt hy).hasMFDerivAt
  have raw := (last.comp (c x) (middle.comp (c x) first)).hasFDerivAt
  let L : E →L[ℝ] E :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (f x))).toContinuousLinearMap.comp
      (D.toContinuousLinearMap.comp ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).comp
        (C.symm.toContinuousLinearMap.comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.toContinuousLinearMap)))
  have typed : HasFDerivAt (d ∘ f ∘ c.symm) L (c x) := raw
  rw [typed.fderiv]
  unfold BundleProjectionCocycleCoordinates.map
  rw [TangentChartTrivialization.forward hy, TangentChartTrivialization.inverse source x hx]
  rfl

end LeanShared.NativeChartCocycleDerivative
