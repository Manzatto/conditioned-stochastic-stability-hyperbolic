module
public import LeanShared.MeasureTheory.CoordinateJacobianDensityProperties
public import LeanShared.MeasureTheory.CoordinateJacobianDensityMeasure

/-! Exact local densities for finite sums of actual weighted coordinate
measures. This also applies to charts transported by a C1 diffeomorphism. -/
public noncomputable section
namespace LeanShared.FiniteChartDensity
open Set MeasureTheory Measure
open scoped Topology ENNReal

@[expose] def measure
    {E M I : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (s : Finset I) (c : I → OpenPartialHomeomorph M E) (p : I → E → ℝ) (μ : Measure E) : Measure M :=
  ∑ i ∈ s, CoordinatePatchMeasure.patch (c i) μ (fun y => ENNReal.ofReal (p i y))

@[expose] def density
    {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (s : Finset I) (c : I → OpenPartialHomeomorph M E) (p : I → E → ℝ)
    (d : OpenPartialHomeomorph M E) (y : E) : ℝ :=
  ∑ i ∈ s, CoordinateJacobianDensity.density (c i) d (p i) y

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
theorem local_measure
    {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (s : Finset I) (c : I → OpenPartialHomeomorph M E) (p : I → E → ℝ)
    (μ : Measure E) [IsAddHaarMeasure μ] (d : OpenPartialHomeomorph M E)
    (smooth : ∀ i ∈ s, ContDiffOn ℝ 1 ((c i).symm.trans d).symm ((c i).symm.trans d).target)
    (continuous : ∀ i ∈ s, Continuous (p i)) (compact : ∀ i ∈ s, HasCompactSupport (p i))
    (support : ∀ i ∈ s, tsupport (p i) ⊆ (c i).target) (nonnegative : ∀ i ∈ s, ∀ y, 0 ≤ p i y) :
    ((measure s c p μ).restrict d.source).map d =
      (μ.restrict d.target).withDensity (fun y => ENNReal.ofReal (density s c p d y)) := by
  classical
  let q := fun i => CoordinateJacobianDensity.density (c i) d (p i)
  have measurableQ i (hi : i ∈ s) : Measurable (fun y => ENNReal.ofReal (q i y)) :=
    (CoordinateJacobianDensity.measurable _ _ _ (smooth i hi) (continuous i hi)
      (compact i hi) (support i hi)).ennreal_ofReal
  have restrictSum : (measure s c p μ).restrict d.source =
      ∑ i ∈ s, (CoordinatePatchMeasure.patch (c i) μ
        (fun y => ENNReal.ofReal (p i y))).restrict d.source :=
    map_sum (Measure.restrictₗ d.source) _ _
  have measurableD : AEMeasurable d ((measure s c p μ).restrict d.source) :=
    d.continuousOn.aemeasurable d.open_source.measurableSet
  rw [restrictSum] at measurableD
  calc
    _ = ∑ i ∈ s, ((CoordinatePatchMeasure.patch (c i) μ
        (fun y => ENNReal.ofReal (p i y))).restrict d.source).map d := by
      rw [restrictSum,Measure.map_finset_sum measurableD]
    _ = ∑ i ∈ s, (μ.restrict d.target).withDensity (fun y => ENNReal.ofReal (q i y)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact CoordinateJacobianDensity.coordinate_measure μ _ d _ (continuous i hi).measurable (smooth i hi)
    _ = (μ.restrict d.target).withDensity (fun y => ∑ i ∈ s, ENNReal.ofReal (q i y)) :=
      (density_sum _ _ _ measurableQ).symm
    _ = _ := by
      congr 1
      funext y
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun i hi => CoordinateJacobianDensity.nonnegative _ _ _ (nonnegative i hi) y)).symm

end LeanShared.FiniteChartDensity
