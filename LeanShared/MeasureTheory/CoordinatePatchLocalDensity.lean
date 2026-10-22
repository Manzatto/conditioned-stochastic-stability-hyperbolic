module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure
public import LeanShared.MeasureTheory.InverseJacobianPushforward

/-! The local coordinate density of an actual weighted chart measure is
calculated from the inverse transition's derivative. -/
public noncomputable section
namespace LeanShared.CoordinatePatchMeasure
open Set MeasureTheory Measure
open scoped ENNReal

theorem coordinate_density
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure E) [IsAddHaarMeasure μ] (e d : OpenPartialHomeomorph M E)
    (p : E → ℝ≥0∞) (measurable : Measurable p)
    (inverse : ContDiffOn ℝ 1 (e.symm.trans d).symm (e.symm.trans d).target) :
    ((patch e μ p).restrict d.source).map d =
      (μ.restrict (e.symm.trans d).target).withDensity
        (fun y => ENNReal.ofReal |(fderiv ℝ (e.symm.trans d).symm y).det| * p ((e.symm.trans d).symm y)) := by
  let A := e.symm.trans d
  let ρ := (μ.restrict A.source).withDensity p
  have measurableInverse : AEMeasurable e.symm ρ := by
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    exact (e.symm.continuousOn.mono (fun _ h => h.1)).aemeasurable A.open_source.measurableSet
  have support : ∀ᵐ x ∂ρ.map e.symm, x ∈ d.source := by
    apply (ae_map_iff measurableInverse d.open_source.measurableSet).mpr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem A.open_source.measurableSet] with x hx
    exact hx.2
  have restrict : (ρ.map e.symm).restrict d.source = ρ.map e.symm :=
    Measure.restrict_eq_self_of_ae_mem support
  have measurableForward : AEMeasurable d (ρ.map e.symm) := by
    rw [←restrict]
    exact d.continuousOn.aemeasurable d.open_source.measurableSet
  rw [restrict_open e μ p d.open_source]
  change (ρ.map e.symm).map d = _
  rw [AEMeasurable.map_map_of_aemeasurable measurableForward measurableInverse]
  exact InverseJacobianPushforward.map_density μ A inverse p measurable

end LeanShared.CoordinatePatchMeasure
