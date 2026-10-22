module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Transport of coordinate density factors through measurable maps. -/
public section
open Set MeasureTheory
open scoped ENNReal
namespace LeanShared.WeightedPushforward
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_withDensity_comp (μ : Measure X) {f : X → Y} (hf : AEMeasurable f μ)
    {q : Y → ℝ≥0∞} (hq : Measurable q) :
    (μ.withDensity (q ∘ f)).map f = (μ.map f).withDensity q := by
  have hfw : AEMeasurable f (μ.withDensity (q ∘ f)) :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  apply Measure.ext_of_lintegral
  intro h hh
  have hhf : AEMeasurable (fun x => h (f x)) μ := hh.comp_aemeasurable hf
  rw [lintegral_map' hh.aemeasurable hfw,
    lintegral_withDensity_eq_lintegral_mul₀ (hq.comp_aemeasurable hf)
      hhf,
    lintegral_withDensity_eq_lintegral_mul _ hq hh,
    lintegral_map' (hq.mul hh).aemeasurable hf]
  rfl
end LeanShared.WeightedPushforward
