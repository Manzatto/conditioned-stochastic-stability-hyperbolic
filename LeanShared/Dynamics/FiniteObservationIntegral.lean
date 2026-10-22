module

public import LeanShared.Dynamics.FiniteObservationEntropy
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Exact integration over the actual law of a finite measurable observation. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I : Type*} [MeasurableSpace X] [Fintype I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

theorem integral_observation (μ : Measure X) [IsFiniteMeasure μ]
    (g : X → I) (mg : Measurable g) (a : I → ℝ) :
    (∫ x, a (g x) ∂μ) = ∑ i, μ.real (g ⁻¹' {i})*a i := by
  rw [←integral_map_of_stronglyMeasurable mg (measurable_of_finite a).stronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.real,Measure.map_apply mg (measurableSet_singleton i)]
  rfl

end LeanShared.FiniteObservationEntropy
