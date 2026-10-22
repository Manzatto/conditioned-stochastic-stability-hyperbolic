module
public import LeanShared.Geometry.NativeRegularInclusion
public import LeanShared.Geometry.SupportedCorePhysicalRealization

/-! Physical restriction of the native full tests to a compact collar, density of their smooth core,
and agreement of the native regular inclusion with the physical realization of a regular
completion. -/
@[expose] public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle BoundedContinuousFunction
namespace LeanShared.NativeFullHolderTests
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (b : ℝ) (hb1 : b ≤ 1)

/-- The physical values of a full test on a collar. -/
def globalPhysical (K : Set M) : Full (E := E) (M := M) b hb1 →L[ℂ] (K →ᵇ ℂ) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact SmoothHolderTestSpaces.physicalOn b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ K

theorem globalPhysical_apply (K : Set M) (v : Full (E := E) (M := M) b hb1) (x : K) :
    globalPhysical b hb1 K v x = view b hb1 v x.val := rfl

theorem core_dense : DenseRange (core (E := E) (M := M) b hb1) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact SmoothHolderTestSpaces.coreMap_dense b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1) univ

theorem core_continuous (c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M)) :
    Continuous (view b hb1 (core b hb1 c)) := by
  change Continuous (fun x => c.val x)
  exact c.property.1.continuous

end LeanShared.NativeFullHolderTests

namespace LeanShared.ManifoldHolderQuotient
variable {E M I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
    (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)

/-- The native inclusion, restricted to a collar, is the physical realization of any regular
core with literal physical values. -/
theorem globalPhysical_includeReg (L : Set M) [CompactSpace L]
    (q : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] Space d hb hb1) (dense : DenseRange q)
    (C : ℝ) (hbound : ∀ c, ‖SmoothSupportedManifoldCore.physicalCore V L c‖ ≤ C * ‖q c‖)
    (hq : ∀ c x, physical d hb hb1 (q c) x = c.val x) (v : Space d hb hb1) :
    NativeFullHolderTests.globalPhysical b hb1.le L (includeReg d hb hb1 atlas v) =
      SmoothSupportedManifoldCore.physicalRealization V L q v := by
  apply BoundedContinuousFunction.ext
  intro x
  rw [NativeFullHolderTests.globalPhysical_apply, view_includeReg]
  symm
  exact SmoothSupportedManifoldCore.physicalRealization_value V L q dense C hbound
    (fun y => (BoundedContinuousFunction.evalCLM ℂ y).comp (physical d hb hb1))
    (fun y c => hq c y) v x

end LeanShared.ManifoldHolderQuotient
