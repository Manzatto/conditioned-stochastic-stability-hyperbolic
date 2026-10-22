module

public import LeanShared.Geometry.TangentChartUniformBounds

/-! The derivative of an actual vector-valued map in a fixed source chart
is precisely its normalized tangent differential composed with the native
inverse tangent chart. The identity permits genuine immersion Gram maps
to use proved coordinate Hölder estimates. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.NativeChartVectorDerivative
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

@[expose] def coordinateDifferential (f : M → F) (center x : M) : E →L[ℝ] F :=
  (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x).comp
      ((trivializationAt E (TangentSpace (𝓘(ℝ,E))) center).symmL ℝ x))

omit [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem fderiv_eq (f : M → F) (differentiable : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,F)) f)
    (source x : M) (hx : x ∈ (chartAt E source).source) :
    fderiv ℝ (f ∘ (chartAt E source).symm) ((chartAt E source) x) =
      coordinateDifferential f source x := by
  let c := chartAt E source
  let C := (CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas source)).mfderiv hx
  have first : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c.symm (c x) C.symm.toContinuousLinearMap :=
    ((CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas source)).mdifferentiableAt_symm
      (c.map_source hx)).hasMFDerivAt
  have middle : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (c.symm (c x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x) := by
    rw [c.left_inv hx]
    exact (differentiable x).hasMFDerivAt
  have raw := (middle.comp (c x) first).hasFDerivAt
  let L : E →L[ℝ] F :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x).comp
        (C.symm.toContinuousLinearMap.comp
          (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.toContinuousLinearMap))
  have typed : HasFDerivAt (f ∘ c.symm) L (c x) := raw
  rw [typed.fderiv]
  unfold coordinateDifferential
  rw [TangentChartTrivialization.inverse source x hx]

end LeanShared.NativeChartVectorDerivative
