module
public import LeanShared.Geometry.ManifoldHolderNativeInclusion
public import LeanShared.Geometry.NativeFullHolderTests

/-! The bounded inclusion of the constructed lower-regularity space into the full native little
Hölder tests: the native inclusion into the supported tests followed by the inclusion of
supported into full tests. Its tests view exactly the physical functions of the lower-regularity
space. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BoundedContinuousFunction
namespace LeanShared.ManifoldHolderQuotient

variable {E M I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
    (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)

/-- The regular-to-full-test inclusion. -/
def includeReg : Space d hb hb1 →L[ℂ] NativeFullHolderTests.Full (E := E) (M := M) b hb1.le := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact (SmoothHolderTestSpaces.includeFull b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V).comp
      (nativeInclusion d hb hb1 atlas)

theorem view_includeReg (v : Space d hb hb1) (x : M) :
    NativeFullHolderTests.view b hb1.le (includeReg d hb hb1 atlas v) x = physical d hb hb1 v x := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact congrArg (fun f : M →ᵇ ℂ => f x) (physical_nativeInclusion d hb hb1 atlas v)

end LeanShared.ManifoldHolderQuotient
