module
public import LeanShared.MeasureTheory.IntrinsicCoordinatePatchMeasures
public import LeanShared.MeasureTheory.CompatibleChartMeasures

/-! Independent atlas construction of the volume induced by an immersion.
The densities use the actual ambient differential, and coordinate overlap
compatibility and atlas independence are proved rather than assumed. -/
public noncomputable section
open Set MeasureTheory Measure
open scoped ENNReal
namespace LeanShared.ImmersionAtlasVolume
variable {U E M : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

structure Atlas (ι : M → E) where
  chart : ℕ → OpenPartialHomeomorph M U
  cover : ⋃ n, (chart n).source = univ
  parametrization : ∀ n, ContDiffOn ℝ 1 (ι ∘ (chart n).symm) (chart n).target
  transition : ∀ i j, ContDiffOn ℝ 1 ((chart i).symm.trans (chart j))
    ((chart i).symm.trans (chart j)).source

variable {ι : M → E}

@[expose] def localMeasure (A : Atlas (U := U) ι) (μ : Measure U) (n : ℕ) : Measure M :=
  CoordinatePatchMeasure.patch (A.chart n) μ
    (IntrinsicCoordinatePatchMeasures.density (ι ∘ (A.chart n).symm) (A.chart n).target)

@[expose] def volume (A : Atlas (U := U) ι) (μ : Measure U) : Measure M :=
  CompatibleChartMeasures.glue (fun n => (A.chart n).source) (localMeasure A μ)

theorem compatible (A : Atlas (U := U) ι) (μ : Measure U) [IsAddHaarMeasure μ] (i j : ℕ) :
    ((localMeasure A μ i).restrict (A.chart i).source).restrict (A.chart j).source =
      ((localMeasure A μ j).restrict (A.chart j).source).restrict (A.chart i).source := by
  simpa only [localMeasure, CoordinatePatchMeasure.restrict_source] using
    IntrinsicCoordinatePatchMeasures.compatible μ (A.chart i) (A.chart j) ι
      (A.transition i j) (A.parametrization j)

theorem restrict_chart (A : Atlas (U := U) ι) (μ : Measure U) [IsAddHaarMeasure μ] (n : ℕ) :
    (volume A μ).restrict (A.chart n).source = localMeasure A μ n := by
  rw [volume, CompatibleChartMeasures.restrict_glue _ _
    (fun i => (A.chart i).open_source.measurableSet) A.cover (compatible A μ) n]
  exact CoordinatePatchMeasure.restrict_source _ _ _

/-- Changing all the charts leaves the constructed induced volume unchanged. -/
theorem atlas_independent (A B : Atlas (U := U) ι) (μ : Measure U) [IsAddHaarMeasure μ]
    (cross : ∀ i j, ContDiffOn ℝ 1 ((A.chart i).symm.trans (B.chart j))
      ((A.chart i).symm.trans (B.chart j)).source) : volume A μ = volume B μ := by
  apply CompatibleChartMeasures.glue_eq_glue _ _ _ _
    (fun i => (A.chart i).open_source.measurableSet)
    (fun j => (B.chart j).open_source.measurableSet) A.cover B.cover
    (compatible A μ) (compatible B μ)
  intro i j
  simpa only [localMeasure, CoordinatePatchMeasure.restrict_source] using
    IntrinsicCoordinatePatchMeasures.compatible μ (A.chart i) (B.chart j) ι
      (cross i j) (B.parametrization j)
end LeanShared.ImmersionAtlasVolume
