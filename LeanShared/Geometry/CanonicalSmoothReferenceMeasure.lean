module
public import LeanShared.Geometry.FiniteSmoothReferenceSupport

/-! A canonical choice of finite smooth auxiliary reference, constructed from
ordinary charts rather than supplied as a measure-regularity assumption. -/
public noncomputable section
open MeasureTheory Measure
namespace LeanShared.FiniteSmoothReferenceCharts
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E]

@[expose] def canonicalData : Data (E := E) (M := M) := Classical.choice exists_data

@[expose] def referenceMeasure (μ : Measure E) : Measure M :=
  (canonicalData (E := E) (M := M)).measure μ

instance reference_finite (μ : Measure E) [IsAddHaarMeasure μ] :
    IsFiniteMeasure (referenceMeasure (M := M) μ) :=
  Data.finite canonicalData μ

instance reference_openPositive (μ : Measure E) [IsAddHaarMeasure μ] :
    IsOpenPosMeasure (referenceMeasure (M := M) μ) :=
  Data.openPositive canonicalData μ
end LeanShared.FiniteSmoothReferenceCharts
