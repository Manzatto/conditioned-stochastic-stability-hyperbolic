module
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! The physical convolution integral and the translation form used by
leaf-volume estimates agree for the actual invariant ambient measure. -/
public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LeanShared.PositiveConvolutionSubstitution
variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
  [MeasurableNeg E]

theorem identity (μ : Measure E) [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (k f : E → ℝ≥0∞) (mk : Measurable k) (mf : Measurable f) (x : E) :
    (∫⁻ y, k (x-y)*f y ∂μ) = ∫⁻ z, k z*f (x-z) ∂μ := by
  have measurableIntegrand : Measurable (fun y => k (x-y)*f y) :=
    (mk.comp (measurable_const.sub measurable_id)).mul mf
  have actual := (μ.measurePreserving_sub_left x).lintegral_comp measurableIntegrand
  simpa only [sub_sub_cancel] using actual.symm

end LeanShared.PositiveConvolutionSubstitution
