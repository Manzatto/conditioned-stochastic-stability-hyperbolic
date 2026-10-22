module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniformly bounded terminal inputs and tests turn a positive orbit
integral upper bound into a complex matrix-coefficient upper bound. -/

public section
open MeasureTheory
open scoped ENNReal

namespace LeanShared.PositiveIntegralCoefficientBound

theorem norm_integral_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (positive : ∀ x, 0 ≤ w x) (f g : X → ℂ)
    (A B U : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U)
    (boundF : ∀ x, ‖f x‖ ≤ A) (boundG : ∀ x, ‖g x‖ ≤ B)
    (upper : (∫⁻ x, ENNReal.ofReal (w x) ∂μ) ≤ ENNReal.ofReal U) :
    ‖∫ x, (w x : ℂ) * f x * g x ∂μ‖ ≤ (A * B) * U := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hA hB) hU)).mp
  calc
    ENNReal.ofReal ‖∫ x, (w x : ℂ) * f x * g x ∂μ‖ ≤
        ∫⁻ x, ENNReal.ofReal ‖(w x : ℂ) * f x * g x‖ ∂μ := by
      simpa only [← ofReal_norm] using enorm_integral_le_lintegral_enorm
        (fun x => (w x : ℂ) * f x * g x)
    _ ≤ ∫⁻ x, ENNReal.ofReal (A * B) * ENNReal.ofReal (w x) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (mul_nonneg hA hB)]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (positive x)]
      calc
        w x * ‖f x‖ * ‖g x‖ ≤ w x * A * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (boundF x) (positive x)) (boundG x)
            (norm_nonneg _) (mul_nonneg (positive x) hA)
        _ = A * B * w x := by ring
    _ = ENNReal.ofReal (A * B) * ∫⁻ x, ENNReal.ofReal (w x) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (A * B) * ENNReal.ofReal U :=
      mul_le_mul le_rfl upper bot_le bot_le
    _ = ENNReal.ofReal (A * B * U) := (ENNReal.ofReal_mul (mul_nonneg hA hB)).symm

end LeanShared.PositiveIntegralCoefficientBound
