module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Actual coordinate-density measures and their restrictions to overlapping
charts. No globally measurable extension of a chart is assumed. -/
public noncomputable section
open Set MeasureTheory Measure
open scoped ENNReal
namespace LeanShared.CoordinatePatchMeasure
variable {M E : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

@[expose] def patch (e : OpenPartialHomeomorph M E) (μ : Measure E) (j : E → ℝ≥0∞) :
    Measure M := ((μ.restrict e.target).withDensity j).map e.symm

theorem inverse_aemeasurable (e : OpenPartialHomeomorph M E)
    (μ : Measure E) (j : E → ℝ≥0∞) :
    AEMeasurable e.symm ((μ.restrict e.target).withDensity j) := by
  apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
  exact e.symm.continuousOn.aemeasurable e.open_target.measurableSet

theorem restrict_source (e : OpenPartialHomeomorph M E)
    (μ : Measure E) (j : E → ℝ≥0∞) : (patch e μ j).restrict e.source = patch e μ j := by
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_map_iff (inverse_aemeasurable e μ j) e.open_source.measurableSet).mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem e.open_target.measurableSet] with x hx
  exact e.map_target hx

theorem restrict_open (e : OpenPartialHomeomorph M E)
    (μ : Measure E) [SFinite μ] (j : E → ℝ≥0∞) {V : Set M} (hV : IsOpen V) :
    (patch e μ j).restrict V =
      ((μ.restrict (e.target ∩ e.symm ⁻¹' V)).withDensity j).map e.symm := by
  rw [patch, Measure.restrict_map_of_aemeasurable (inverse_aemeasurable e μ j) hV.measurableSet,
    restrict_withDensity', Measure.restrict_restrict' e.open_target.measurableSet, inter_comm]
end LeanShared.CoordinatePatchMeasure
