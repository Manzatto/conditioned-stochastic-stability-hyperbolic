module
public import LeanShared.MeasureTheory.WeightedPushforward
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Weighted coordinate change for intrinsic volume. The Jacobian and
pushforward identity are derived from the actual differential. -/
public noncomputable section
open Set MeasureTheory Measure
open scoped ENNReal
namespace LeanShared.WeightedJacobianTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem map_density (μ : Measure E) [IsAddHaarMeasure μ]
    {s : Set E} (hs : MeasurableSet s) {f : E → E} {D : E → E →L[ℝ] E}
    (derivative : ∀ x ∈ s, HasFDerivWithinAt f (D x) s x) (injective : InjOn f s)
    {q : E → ℝ≥0∞} (hq : Measurable q) :
    ((μ.restrict s).withDensity
      (fun x => ENNReal.ofReal |(D x).det| * q (f x))).map f =
      (μ.restrict (f '' s)).withDensity q := by
  have hf : AEMeasurable f (μ.restrict s) :=
    ContinuousOn.aemeasurable₀ (fun x hx =>
      (derivative x hx).differentiableWithinAt.continuousWithinAt) hs.nullMeasurableSet
  have hJ : AEMeasurable (fun x => ENNReal.ofReal |(D x).det|) (μ.restrict s) :=
    aemeasurable_ofReal_abs_det_fderivWithin μ hs derivative
  rw [show (fun x => ENNReal.ofReal |(D x).det| * q (f x)) =
    (fun x => ENNReal.ofReal |(D x).det|) * (q ∘ f) from rfl,
    withDensity_mul₀ hJ (hq.comp_aemeasurable hf),
    WeightedPushforward.map_withDensity_comp _
      (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hq,
    map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet derivative injective]
end LeanShared.WeightedJacobianTransport
