module

public import LeanShared.Geometry.FiniteSmoothReferenceLocalMeasure
public import LeanShared.MeasureTheory.CoordinateMeasureRecovery
public import LeanShared.MeasureTheory.CoordinatePatchVolumeBound

/-! The constructed smooth reference measure uniformly dominates inverse
chart Haar volume on every compact chart target patch. Density positivity,
coordinate representation and the bound are all proved internally. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

theorem Data.exists_compact_inverse_volume_bound
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (K : Set E) (compact : IsCompact K) (inside : K ⊆ c.target) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ (μ.restrict K).map c.symm ≤ C • d.measure μ := by
  have recovery := CoordinateMeasureRecovery.recover c ((d.measure μ).restrict c.source)
    (ae_restrict_mem c.open_source.measurableSet)
  rw [d.local_measure μ c hc] at recovery
  have reference : (d.measure μ).restrict c.source =
      CoordinatePatchMeasure.patch c μ (fun y => ENNReal.ofReal (d.localDensity c y)) := recovery.symm
  exact CoordinatePatchMeasure.exists_inverse_compact_volume_bound c μ (d.measure μ)
    (d.localDensity c) compact inside ((d.localDensity_continuousOn c hc).mono inside)
    (fun y hy => d.localDensity_positive c hc y (inside hy)) reference

end LeanShared.FiniteSmoothReferenceCharts
