module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual zero-mean convolution cancellation against a Hölder function.
This gives the high-frequency regularity gain from the literal integral,
rather than assuming a Cv-to-dyadic norm estimate. -/
public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.HolderConvolutionCancellation
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

theorem bound (k : E → ℂ) (integrable : Integrable k μ) (zero : ∫ y, k y ∂μ = 0)
    (f : E →ᵇ ℂ) {a C : ℝ} (_hC : 0 ≤ C)
    (moment : Integrable (fun y => ‖k y‖ * ‖y‖ ^ a) μ)
    (holder : ∀ x y, ‖f x-f y‖ ≤ C * ‖x-y‖ ^ a) (x : E) :
    ‖∫ y, k y * f (x-y) ∂μ‖ ≤ C * ∫ y, ‖k y‖ * ‖y‖ ^ a ∂μ := by
  have product : Integrable (fun y => k y * f (x-y)) μ :=
    integrable.mul_bdd
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => f.norm_coe_le_norm (x-y))
  have subtract : (∫ y, k y * (f (x-y)-f x) ∂μ) = ∫ y, k y * f (x-y) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub product (integrable.mul_const (f x)), integral_mul_const, zero, zero_mul, sub_zero]
  rw [← subtract]
  calc
    _ ≤ ∫ y, ‖k y * (f (x-y)-f x)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * (‖k y‖ * ‖y‖ ^ a) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
        (moment.const_mul C) (ae_of_all _ fun y => by
          have estimate : ‖f (x-y)-f x‖ ≤ C * ‖y‖ ^ a := by
            simpa only [sub_sub_cancel_left, norm_neg] using holder (x-y) x
          change ‖k y * (f (x-y)-f x)‖ ≤ C * (‖k y‖ * ‖y‖ ^ a)
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left estimate (norm_nonneg _)).trans_eq (by ring))
    _ = _ := integral_const_mul _ _
end LeanShared.HolderConvolutionCancellation
