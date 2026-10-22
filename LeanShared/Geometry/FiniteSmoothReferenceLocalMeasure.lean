module
public import LeanShared.Geometry.FiniteSmoothReferenceLocalDensity
import all LeanShared.Geometry.FiniteSmoothReferenceLocalDensity

/-! The positive continuous local density constructed from the chart bumps
represents the EXACT reference measure in each actual smooth chart. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff ENNReal

private theorem density_sum {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ≥0∞)
    (measurable : ∀ i ∈ s, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.withDensity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact withDensity_zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [show (fun x => f i x + ∑ j ∈ s, f j x) = f i + (fun x => ∑ j ∈ s, f j x) from rfl,
      withDensity_add_left (measurable i (Finset.mem_insert_self _ _)),
      ih (fun j hj => measurable j (Finset.mem_insert_of_mem hj))]

set_option maxHeartbeats 1600000 in
theorem Data.local_measure
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ((d.measure μ).restrict c.source).map c =
      (μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (d.localDensity c y)) := by
  classical
  let q := fun x => CoordinateJacobianDensity.density (chartAt E x) c (d.density x)
  have measurableQ (x : M) : Measurable (fun y => ENNReal.ofReal (q x y)) :=
    (CoordinateJacobianDensity.measurable _ _ _
      (transition_regular _ _ (chart_mem_maximalAtlas x) hc)
      (d.smooth x).continuous (d.compact_support x) (d.support x)).ennreal_ofReal
  have restrictSum : (d.measure μ).restrict c.source =
      ∑ x ∈ d.index, (CoordinatePatchMeasure.patch (chartAt E x) μ
        (fun y => ENNReal.ofReal (d.density x y))).restrict c.source := by
    exact map_sum (Measure.restrictₗ c.source) _ _
  have measurableC : AEMeasurable c ((d.measure μ).restrict c.source) :=
    c.continuousOn.aemeasurable c.open_source.measurableSet
  rw [restrictSum] at measurableC
  calc
    _ = ∑ x ∈ d.index, ((CoordinatePatchMeasure.patch (chartAt E x) μ
        (fun y => ENNReal.ofReal (d.density x y))).restrict c.source).map c := by
      rw [restrictSum,Measure.map_finset_sum measurableC]
    _ = ∑ x ∈ d.index, (μ.restrict c.target).withDensity (fun y => ENNReal.ofReal (q x y)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact CoordinateJacobianDensity.coordinate_measure μ _ c _ (d.smooth x).continuous.measurable
        (transition_regular _ _ (chart_mem_maximalAtlas x) hc)
    _ = (μ.restrict c.target).withDensity (fun y => ∑ x ∈ d.index, ENNReal.ofReal (q x y)) :=
      (density_sum _ _ _ (fun x _ => measurableQ x)).symm
    _ = _ := by
      congr 1
      funext y
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun x _ => CoordinateJacobianDensity.nonnegative _ _ _ (fun z => (d.bounds x z).1) y)).symm

end LeanShared.FiniteSmoothReferenceCharts
