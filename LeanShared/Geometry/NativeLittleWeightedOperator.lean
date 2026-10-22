module
public import LeanShared.Geometry.NativeLittleWeightedAction

/-! The actual weighted map on the native smooth-core completion, with
literal physical action and its quantitative operator norm. -/
public noncomputable section
namespace LeanShared.SmoothHolderTestSpaces
open Set IsManifold Bundle MeasureTheory
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem exists_weighted_operator
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
    (ψ : M →ᵇ ℂ) (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u ψ)
    (support : tsupport ψ ⊆ V) (F : M → M)
    (hF : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)
    {C : ℝ} (hC : 0 ≤ C)
    (holder : let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
      ∀ x y, ‖ψ x-ψ y‖ ≤ C*dist x y^b)
    {L : NNReal} (lip : let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
      LipschitzWith L F) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    ∃ A : space b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V →L[ℂ]
        space b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V,
      (∀ v x, physical b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V
        (A v) x = ψ x*physical b
          (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V v (F x)) ∧
      ‖A‖ ≤ max ‖ψ‖ (‖ψ‖*(L:ℝ)^b+C) := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let certificate := BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le
  let full := HolderWeightComposition.operator hb.le ψ hC holder F lip
  let A : space b certificate V →L[ℂ] space b certificate V :=
    (full.comp (space b certificate V).subtypeL).codRestrict _
      (weighted_operator_mem μ e D atlas openV region hb hb1 hbu hu1 ψ regular support F hF hC holder lip)
  refine ⟨A,fun v x => ?_,?_⟩
  · exact HolderWeightComposition.physical_operator hb.le ψ hC holder F lip v.val x
  · apply ContinuousLinearMap.opNorm_le_bound _ (le_trans (norm_nonneg ψ) (le_max_left _ _))
    intro v
    exact HolderWeightComposition.lifted_norm hb.le ψ hC holder F lip v.val

end LeanShared.SmoothHolderTestSpaces
