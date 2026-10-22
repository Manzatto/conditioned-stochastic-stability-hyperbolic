module
public import LeanShared.MeasureTheory.ImmersionAtlasVolume

/-! The independently constructed volume has the intrinsic density in every
compatible chart, not just the countable atlas used in its definition. -/
public noncomputable section
open Set MeasureTheory Measure
namespace LeanShared.ImmersionAtlasVolume
variable {U E M : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  {ι : M → E}

theorem restrict_compatible_chart (A : Atlas (U := U) ι)
    (μ : Measure U) [IsAddHaarMeasure μ] (e : OpenPartialHomeomorph M U)
    (parametrization : ContDiffOn ℝ 1 (ι ∘ e.symm) e.target)
    (cross : ∀ n, ContDiffOn ℝ 1 ((A.chart n).symm.trans e)
      ((A.chart n).symm.trans e).source) :
    (volume A μ).restrict e.source = CoordinatePatchMeasure.patch e μ
      (IntrinsicCoordinatePatchMeasures.density (ι ∘ e.symm) e.target) := by
  apply CompatibleChartMeasures.unique (fun n => (A.chart n).source) A.cover
  intro n
  rw [Measure.restrict_comm (A.chart n).open_source.measurableSet, restrict_chart]
  exact IntrinsicCoordinatePatchMeasures.compatible μ (A.chart n) e ι
    (cross n) parametrization
end LeanShared.ImmersionAtlasVolume
