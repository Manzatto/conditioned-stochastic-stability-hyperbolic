module
public import LeanShared.Geometry.NativeSmoothWeightedHolderCore
public import LeanShared.Analysis.HolderWeightCompositionNorm

/-! Literal weighted composition preserves the native little completion.
Membership follows from genuine fractional smoothing of smooth inputs,
and continuity then extends it to every completed input. -/
public noncomputable section
namespace LeanShared.SmoothHolderTestSpaces
open Set IsManifold Bundle MeasureTheory
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem weighted_operator_mem
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
    ∀ v : space b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V,
      HolderWeightComposition.operator hb.le ψ hC holder F lip v.val ∈
        space b (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  let certificate := BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le
  let A := (HolderWeightComposition.operator hb.le ψ hC holder F lip).comp
    (space b certificate V).subtypeL
  change ∀ v : space b certificate V, A v ∈ space b certificate V
  intro v
  apply (coreMap_dense b certificate V).induction_on
    (p := fun z => A z ∈ space b certificate V) v
    (((holderCore b certificate V).range.isClosed_topologicalClosure).preimage A.continuous)
  intro c
  obtain ⟨z,hz⟩ := exists_weighted_native_core μ e D atlas openV region hb hb1 hbu hu1
    regular support F hF c
  have identity : A (coreMap b certificate V c) = z.val := by
    apply BoundedHolderSpace.physical_injective M b
    ext x
    change BoundedHolderSpace.physical M b
      (HolderWeightComposition.operator hb.le ψ hC holder F lip
        (coreMap b certificate V c).val) x = _
    rw [HolderWeightComposition.physical_operator]
    exact (hz x).symm
  rw [identity]
  exact z.property

end LeanShared.SmoothHolderTestSpaces
