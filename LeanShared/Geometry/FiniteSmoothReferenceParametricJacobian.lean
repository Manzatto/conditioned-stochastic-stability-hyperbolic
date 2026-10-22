module
public import LeanShared.Geometry.FiniteSmoothReferenceParametricDensity
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianLocal

/-! Joint control/state continuity of the actual reference Jacobian. Only
legal controls need define diffeomorphisms; the C1 inverse map is available
on an ambient open neighborhood. No continuity in the noise scale is used. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold Filter
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 2400000 in
theorem Data.parametricJacobian_continuous
    {B A E M : Type*} [TopologicalSpace B]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (a : B → A) (continuousA : Continuous a)
    (H : B → M ≃ₜ M)
    (forward : ∀ b, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H b))
    (inverse : ∀ b, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H b).symm)
    (Φ : A × M → M) (O : Set A) (openO : IsOpen O)
    (inside : ∀ b, a b ∈ O)
    (joint : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 Φ (O ×ˢ univ))
    (same : ∀ b x, Φ (a b,x) = (H b).symm x) :
    Continuous (fun q : B × M => d.jacobian (H q.1) q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let c := chartAt E q.2
  have hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M := chart_mem_maximalAtlas q.2
  have member : q.2 ∈ c.source := mem_chart_source E q.2
  have coordinate : ContinuousAt (fun z : B × M => (a z.1,c z.2)) q :=
    (continuousA.continuousAt.comp continuous_fst.continuousAt).prodMk
      ((c.continuousOn q.2 member).continuousAt (c.open_source.mem_nhds member)
        |>.comp continuous_snd.continuousAt)
  have parameter : ContinuousAt (d.parametricDensity Φ c) (a q.1,c q.2) := (d.parametricDensity_continuousOn Φ c hc O openO joint
    (a q.1,c q.2) ⟨inside q.1,c.map_source member⟩).continuousAt
      ((openO.prod c.open_target).mem_nhds ⟨inside q.1,c.map_source member⟩)
  have numerator : ContinuousAt (fun z : B × M => d.parametricDensity Φ c (a z.1,c z.2)) q :=
    parameter.comp (f := fun z : B × M => (a z.1,c z.2)) coordinate
  have denominator : ContinuousAt (fun z : B × M => d.localDensity c (c z.2)) q := ((d.localDensity_continuousOn c hc (c q.2) (c.map_source member)).continuousAt
    (c.open_target.mem_nhds (c.map_source member))).comp (f := fun z : B × M => c z.2)
    ((c.continuousOn q.2 member).continuousAt (c.open_source.mem_nhds member)
      |>.comp continuous_snd.continuousAt)
  have ratio := numerator.div denominator (d.localDensity_positive c hc _ (c.map_source member)).ne'
  apply ratio.congr_of_eventuallyEq
  have near : ∀ᶠ z : B × M in 𝓝 q, z.2 ∈ c.source :=
    continuous_snd.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds member)
  filter_upwards [near] with z hz
  change d.jacobian (H z.1) z.2 = d.parametricDensity Φ c (a z.1,c z.2) / d.localDensity c (c z.2)
  rw [d.parametricDensity_eq_pushforward Φ (H z.1) (a z.1) (same z.1) c (c z.2)]
  exact d.jacobian_eq_chart_ratio μ (H z.1) (forward z.1) (inverse z.1) c hc hz

end LeanShared.FiniteSmoothReferenceCharts
