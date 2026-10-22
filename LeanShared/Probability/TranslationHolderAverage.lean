module
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Abel

/-! A probability average of translations preserves an actual Hölder
increment estimate. Small supported translation noise gives the quantitative
uniform approximation bound used by mollifier regularization. -/
public noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace LeanShared.TranslationHolderAverage
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsProbabilityMeasure μ] (f : E →ᵇ ℂ)

/-- The literal probability average of translated function values. -/
@[expose] def average (x : E) : ℂ := ∫ w, f (x - w) ∂μ

private theorem integrable_translate (x : E) : Integrable (fun w => f (x - w)) μ :=
  (f.compContinuous ⟨fun w => x - w, continuous_const.sub continuous_id⟩).integrable μ

/-- No regularity of the probability density is used for the Hölder bound. -/
theorem increment_bound {a C : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) (x y : E) :
    ‖average μ f x - average μ f y‖ ≤ C * ‖x - y‖ ^ a := by
  rw [average, average, ← integral_sub (integrable_translate μ f x) (integrable_translate μ f y)]
  have bound : ∀ᵐ w ∂μ, ‖f (x - w) - f (y - w)‖ ≤ C * ‖x - y‖ ^ a :=
    Eventually.of_forall fun w => by
      have h := hf (x - w) (y - w)
      have eq : x - w - (y - w) = x - y := by abel
      rwa [eq] at h
  simpa using norm_integral_le_of_norm_le_const bound

/-- The error is bounded by the actual noise radius to the original
Hölder exponent, uniformly in the evaluation point. -/
theorem error_bound {a C r : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a)
    (support : ∀ᵐ w ∂μ, ‖w‖ ≤ r) (x : E) :
    ‖average μ f x - f x‖ ≤ C * r ^ a := by
  have eq : (∫ w, f (x - w) - f x ∂μ) = average μ f x - f x := by
    rw [integral_sub (integrable_translate μ f x) (integrable_const _)]
    simp [average]
  rw [← eq]
  have bound : ∀ᵐ w ∂μ, ‖f (x - w) - f x‖ ≤ C * r ^ a := by
    filter_upwards [support] with w hw
    have h := hf (x - w) x
    have norm_eq : ‖x - w - x‖ = ‖w‖ := by
      have eq' : x - w - x = -w := by abel
      rw [eq', norm_neg]
    rw [norm_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hw ha) hC)
  simpa using norm_integral_le_of_norm_le_const bound
end LeanShared.TranslationHolderAverage
