module
public import LeanShared.Geometry.ManifoldHolderNativeMembership
public import LeanShared.Geometry.ManifoldSmoothWeightedHolderCore

/-! A genuinely fractional supported weight and a C1 map preserve the native
little Holder core at every strictly smaller exponent. Both the smooth
approximation and the coordinate-to-native completion step are proved. -/
public noncomputable section
namespace LeanShared.SmoothHolderTestSpaces
open Set IsManifold Bundle MeasureTheory
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem exists_weighted_native_core
    {E M J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (μ : Measure E) [μ.IsAddHaarMeasure] {V S : Set M}
    (e : J → OpenPartialHomeomorph M E) (D : ConstructedManifoldLocalization.Data e S)
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (openV : IsOpen V) (region : V ⊆ S)
    {b u : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbu : b < u) (hu1 : u < 1)
    {w : M → ℂ} (hw : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u w)
    (support : tsupport w ⊆ V) (F : M → M)
    (hF : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)
    (c : SmoothSupportedManifoldCore.core (E := E) V) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ z : space b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V,
      ∀ x : M, physical b
        (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V z x =
        w x*c.val (F x) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  obtain ⟨v,identity⟩ := ManifoldSmoothHolderCore.exists_weighted_core_lower μ e D atlas
    openV region hb hb1 hbu hu1 hw support F hF c
  obtain ⟨z,hz⟩ := ManifoldHolderQuotient.exists_native
    (ManifoldSmoothHolderCore.regions e D openV) hb hb1 (fun i => atlas i) v
  refine ⟨z,fun x => ?_⟩
  rw [hz]
  exact identity x

end LeanShared.SmoothHolderTestSpaces
