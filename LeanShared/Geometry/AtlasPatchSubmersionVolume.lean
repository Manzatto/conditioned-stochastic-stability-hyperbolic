module
public import LeanShared.Geometry.AtlasControlSubmersionCoordinates
public import LeanShared.Analysis.LocalPositiveChartSubmersionVolume

/-! The local volume theorem in arbitrary genuine atlas charts. Finite sums
of bounded chart-volume patches can therefore serve as a constructed reference. -/
public noncomputable section
namespace LeanShared.ControlSubmersionCoordinates
open Set MeasureTheory Filter IsManifold
open scoped ENNReal Topology ContDiff Manifold

theorem exists_local_atlas_patch_volume_bound
    {E A M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace M] [BorelSpace M]
    (ρ : Measure A) [ρ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure] (σ : Measure M)
    {H : M × A → M} {x : M} {a : A}
    (smooth : ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a))
    (rank : Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun b => H (x, b)) a))
    (e : OpenPartialHomeomorph M E) (atlas : e ∈ maximalAtlas (𝓘(ℝ, E)) 1 M)
    (source : H (x, a) ∈ e.source) (r : E → ℝ)
    (patchBound : CoordinatePatchMeasure.patch e ν (fun y => ENNReal.ofReal (r y)) ≤ σ)
    (continuousR : ContinuousOn r e.target)
    (positiveR : 0 < r (e (H (x, a)))) :
    ∃ U : Set M, ∃ V : Set A, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ a ∈ V ∧
      ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ y ∈ U, ∀ B : Set M, MeasurableSet B →
        ρ ((fun b => H (y, b)) ⁻¹' B ∩ V) ≤ C * σ B := by
  let c := chartAt E x
  let d := e
  let f : E × A → E := fun z => d (H (Prod.map c.symm id z))
  have cx : x ∈ c.source := mem_chart_source E x
  have dx : H (x, a) ∈ d.source := source
  have target : f (c x, a) ∈ d.target := by
    change d (H (c.symm (c x), a)) ∈ d.target
    rw [c.left_inv cx]
    exact d.map_source dx
  have positivePoint : 0 < r (f (c x, a)) := by
    change 0 < r (e (H (c.symm (c x), a)))
    rw [c.left_inv cx]
    exact positiveR
  obtain ⟨ε, positiveε, C, finiteC, bound⟩ :=
    SubmersionLinearCoordinates.exists_local_positive_chart_bound ν ρ ν σ d r patchBound continuousR
      (atlas_chart_contDiffAt smooth e atlas source)
      (atlas_chart_control_fderiv_surjective smooth rank e atlas source) target
      positivePoint
  have cContinuous : ContinuousAt c x := c.continuousOn.continuousAt (c.open_source.mem_nhds cx)
  have near : {z : M × A | z.1 ∈ c.source ∧ c z.1 ∈ Metric.ball (c x) ε ∧
      H z ∈ d.source ∧ z.2 ∈ Metric.ball a ε} ∈ 𝓝 (x, a) := by
    have stateSource : ∀ᶠ z : M × A in 𝓝 (x, a), z.1 ∈ c.source :=
      continuous_fst.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds cx)
    have coordinateBall : ∀ᶠ z : M × A in 𝓝 (x, a), c z.1 ∈ Metric.ball (c x) ε :=
      (cContinuous.comp continuous_fst.continuousAt).preimage_mem_nhds
        (Metric.ball_mem_nhds _ positiveε)
    have targetSource : ∀ᶠ z : M × A in 𝓝 (x, a), H z ∈ d.source :=
      smooth.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds dx)
    have controlBall : ∀ᶠ z : M × A in 𝓝 (x, a), z.2 ∈ Metric.ball a ε :=
      continuous_snd.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ positiveε)
    exact stateSource.and (coordinateBall.and (targetSource.and controlBall))
  obtain ⟨U, hU, V, hV, contained⟩ := mem_nhds_prod_iff.mp near
  obtain ⟨U₀, subsetU, openU, memberU⟩ := mem_nhds_iff.mp hU
  obtain ⟨V₀, subsetV, openV, memberV⟩ := mem_nhds_iff.mp hV
  refine ⟨U₀, V₀, openU, openV, memberU, memberV, C, finiteC, ?_⟩
  intro y hy B measurableB
  have state := contained (show (y, a) ∈ U ×ˢ V from ⟨subsetU hy, subsetV memberV⟩)
  calc
    ρ ((fun b => H (y, b)) ⁻¹' B ∩ V₀) ≤
        ρ ((fun b => d.symm (f (c y, b))) ⁻¹' B ∩ Metric.ball a ε) := by
      apply measure_mono
      intro b hb
      have properties := contained (show (y, b) ∈ U ×ˢ V from ⟨subsetU hy, subsetV hb.2⟩)
      refine ⟨?_, properties.2.2.2⟩
      change d.symm (d (H (c.symm (c y), b))) ∈ B
      rw [c.left_inv properties.1, d.left_inv properties.2.2.1]
      exact hb.1
    _ ≤ C * σ B := bound (c y) state.2.1 B measurableB

end LeanShared.ControlSubmersionCoordinates
