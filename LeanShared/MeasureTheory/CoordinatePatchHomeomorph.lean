module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Pushforward of an actual coordinate measure by a homeomorphism is the
same weighted coordinate measure in the transported chart. -/
public noncomputable section
namespace LeanShared.CoordinatePatchMeasure
open Set MeasureTheory Measure
open scoped ENNReal

theorem map_homeomorph
    {E M : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (H : M ≃ₜ M) (e : OpenPartialHomeomorph M E) (μ : Measure E) (p : E → ℝ≥0∞) :
    (patch e μ p).map H = patch (H.symm.transOpenPartialHomeomorph e) μ p := by
  rw [patch, AEMeasurable.map_map_of_aemeasurable H.continuous.measurable.aemeasurable
    (inverse_aemeasurable e μ p)]
  rfl

end LeanShared.CoordinatePatchMeasure
