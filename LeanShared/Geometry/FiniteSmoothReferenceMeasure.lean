module
public import LeanShared.Geometry.FiniteSmoothReferenceCharts
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! A genuine finite smooth auxiliary volume is the sum of finitely many
compactly supported smooth coordinate densities, with no supplied measure. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped Topology ContDiff Manifold ENNReal
namespace LeanShared.FiniteSmoothReferenceCharts
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace E] [BorelSpace E]

@[expose] def Data.measure (d : Data (E := E) (M := M)) (μ : Measure E) : Measure M :=
  ∑ x ∈ d.index, CoordinatePatchMeasure.patch (chartAt E x) μ (fun y => ENNReal.ofReal (d.density x y))

omit [FiniteDimensional ℝ E] [CompactSpace M] [BorelSpace M] [BorelSpace E] in
theorem Data.patch_le (d : Data (E := E) (M := M)) (μ : Measure E) {x : M} (hx : x ∈ d.index) :
    CoordinatePatchMeasure.patch (chartAt E x) μ (fun y => ENNReal.ofReal (d.density x y)) ≤ d.measure μ := by
  classical
  exact Finset.single_le_sum (f := fun x => CoordinatePatchMeasure.patch (chartAt E x) μ
    (fun y => ENNReal.ofReal (d.density x y))) (fun i _ => show (0 : Measure M) ≤ _ from Measure.zero_le _) hx

instance Data.finite (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsFiniteMeasure (d.measure μ) := by
  classical
  have finitePatch (x : M) : IsFiniteMeasure
      (CoordinatePatchMeasure.patch (chartAt E x) μ (fun y => ENNReal.ofReal (d.density x y))) := by
    have integrable : Integrable (d.density x) μ :=
      (d.smooth x).continuous.integrable_of_hasCompactSupport (d.compact_support x)
    have integral_lt : ∫⁻ y, ENNReal.ofReal (d.density x y) ∂μ.restrict (chartAt E x).target < (∞ : ℝ≥0∞) :=
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => (d.bounds x y).1))).mp
        integrable.integrableOn.hasFiniteIntegral
    let : IsFiniteMeasure ((μ.restrict (chartAt E x).target).withDensity
        (fun y => ENNReal.ofReal (d.density x y))) := isFiniteMeasure_withDensity integral_lt.ne
    change IsFiniteMeasure (Measure.map (chartAt E x).symm _ )
    infer_instance
  unfold Data.measure
  infer_instance
end LeanShared.FiniteSmoothReferenceCharts
