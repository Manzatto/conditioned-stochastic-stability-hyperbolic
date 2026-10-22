module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedCompactControlSubmersion
public import LeanShared.Geometry.CanonicalSmoothReferenceMeasure

/-! The full ordinary noise source is available without a supplied reference
measure, smoothing theorem, endpoint-open theorem, or volume comparison. -/
public noncomputable section
open MeasureTheory
open scoped Manifold ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

theorem canonical_controlSubmersionSources
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [Fintype ι] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    ControlSubmersionSources (E := E) (ι := ι)
      (LeanShared.FiniteSmoothReferenceCharts.referenceMeasure (M := M) ν) :=
  controlSubmersionSources_of_finite_reference LeanShared.FiniteSmoothReferenceCharts.canonicalData ν

theorem exists_finite_reference_controlSubmersionSources
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [Fintype ι] [MeasurableSpace M] [BorelSpace M] :
    ∃ σ : Measure M, IsFiniteMeasure σ ∧ σ.IsOpenPosMeasure ∧
      ControlSubmersionSources (E := E) (ι := ι) σ := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let ν : Measure E := Measure.addHaar
  exact ⟨LeanShared.FiniteSmoothReferenceCharts.referenceMeasure (M := M) ν,
    inferInstance, inferInstance, canonical_controlSubmersionSources ν⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
