module
public import LeanShared.Geometry.EuclideanLittleChartNativeExtension
import all LeanShared.Geometry.EuclideanLittleChartNativeExtension
public import LeanShared.Geometry.ManifoldHolderQuotient

/-! Finite chart reconstruction preserves the genuine native little Holder
completion. This is derived from chartwise smooth approximation; it is not
an assumed identification of completed norms. -/
public noncomputable section
namespace LeanShared.ManifoldHolderQuotient
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction BigOperators

set_option maxHeartbeats 1600000 in
theorem exists_native
    {E M I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
    (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (v : Space d hb hb1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ z : SmoothHolderTestSpaces.space b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V,
      SmoothHolderTestSpaces.physical b
        (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V z =
      physical d hb hb1 v := by
  classical
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let : NormedAddCommGroup (Coordinates d hb hb1) := inferInstance
  let : SeminormedAddCommGroup (Coordinates d hb hb1) :=
    (inferInstance : NormedAddCommGroup (Coordinates d hb hb1)).toSeminormedAddCommGroup
  let : NormedSpace ℂ (Coordinates d hb hb1) := inferInstance
  obtain ⟨c,rfl⟩ := BanachFunctionQuotient.quotient_surjective (reconstruction d hb hb1) v
  let chart (i : I) := EuclideanLittleChartExtension.nativeExtension hb hb1
    (d.compact_closure i) (e i) (d.closure_target i) (atlas i)
    (by rintro _ ⟨y,hy,rfl⟩; exact d.inverse_region i y hy) (c i)
  refine ⟨∑ i, chart i, ?_⟩
  rw [map_sum]
  ext x
  rw [BoundedContinuousFunction.sum_apply]
  change (∑ i, SmoothHolderTestSpaces.physical b _ V (chart i) x) =
    FiniteHolderChartPatching.reconstruction b (fun i => closure (d.region i))
      d.compact_closure e d.closure_target (supportedCoordinates d hb hb1 c) x
  rw [FiniteHolderChartPatching.reconstruction_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold chart EuclideanLittleChartExtension.nativeExtension
  change BoundedHolderSpace.physical M b
    (EuclideanLittleChartExtension.nativeGraph hb hb1 (d.compact_closure i)
      (e i) (d.closure_target i) (atlas i) (c i)) x = _
  rw [EuclideanLittleChartExtension.nativeGraph_physical]
  rfl

end LeanShared.ManifoldHolderQuotient
