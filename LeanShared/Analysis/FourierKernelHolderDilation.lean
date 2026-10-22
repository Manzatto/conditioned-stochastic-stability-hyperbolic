module
public import LeanShared.Analysis.FourierSchwartzKernel

/-! Exact fractional moment scaling of the literal Fourier kernels.
The determinant factor in ambient Lebesgue change of variables cancels
the kernel normalization, leaving precisely the regularity gain r^-a. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_norm_rpow_kernel_dilateSymbol (σ : 𝓢(E,ℂ))
    (r : ℝ) (hr : 0 < r) (a : ℝ) :
    (∫ y, ‖kernel (dilateSymbol σ r hr) y‖ * ‖y‖ ^ a) =
      (r ^ a)⁻¹ * ∫ y, ‖kernel σ y‖ * ‖y‖ ^ a := by
  have positive : 0 < r ^ a := Real.rpow_pos_of_pos hr _
  have scale (y : E) : ‖kernel (dilateSymbol σ r hr) y‖ * ‖y‖ ^ a =
      (r ^ Module.finrank ℝ E) * (r ^ a)⁻¹ *
        (‖kernel σ (r • y)‖ * ‖r • y‖ ^ a) := by
    rw [kernel_dilateSymbol, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hr _),
      norm_smul, Real.norm_eq_abs, abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg _)]
    field_simp
  simp_rw [scale]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (fun y : E => ‖kernel σ y‖ * ‖y‖ ^ a) r (hR := hr.le), smul_eq_mul]
  have dim : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp
end LeanShared.FourierSchwartzKernel
