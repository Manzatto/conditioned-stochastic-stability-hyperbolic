module
public import LeanShared.MeasureTheory.CoordinateJacobianDensity

/-! The continuous zero-extended coordinate Jacobian density represents the
actual local pushforward measure, not an arbitrarily assigned density. -/
public noncomputable section
namespace LeanShared.CoordinateJacobianDensity
open Set MeasureTheory Measure
open scoped ENNReal

theorem coordinate_measure
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure E) [IsAddHaarMeasure μ] (e d : OpenPartialHomeomorph M E)
    (p : E → ℝ) (measurable : Measurable p)
    (inverse : ContDiffOn ℝ 1 (e.symm.trans d).symm (e.symm.trans d).target) :
    ((CoordinatePatchMeasure.patch e μ (fun x => ENNReal.ofReal (p x))).restrict d.source).map d =
      (μ.restrict d.target).withDensity (fun y => ENNReal.ofReal (density e d p y)) := by
  classical
  let A := e.symm.trans d
  have weights : (fun y => ENNReal.ofReal (density e d p y)) =
      A.target.indicator (fun y => ENNReal.ofReal |(fderiv ℝ A.symm y).det| *
        ENNReal.ofReal (p (A.symm y))) := by
    funext y
    by_cases hy : y ∈ A.target
    · change ENNReal.ofReal (if y ∈ A.target then _ else _) = _
      rw [ite_eq_left hy,indicator_of_mem hy,ENNReal.ofReal_mul (abs_nonneg _)]
    · change ENNReal.ofReal (if y ∈ A.target then _ else _) = _
      rw [ite_eq_right hy,indicator_of_notMem hy,ENNReal.ofReal_zero]
  rw [weights,withDensity_indicator A.open_target.measurableSet,
    Measure.restrict_restrict' d.open_target.measurableSet,
    inter_eq_left.mpr (show A.target ⊆ d.target from fun _ h => h.1)]
  exact CoordinatePatchMeasure.coordinate_density μ e d _ measurable.ennreal_ofReal inverse

end LeanShared.CoordinateJacobianDensity
