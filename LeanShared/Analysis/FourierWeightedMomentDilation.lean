module
public import LeanShared.Analysis.FourierKernelHolderDilation
public import LeanShared.Analysis.SchwartzWeightedHolderMoment

/-! The radial-envelope moment of an actual dilated Fourier kernel gains r^-a. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_weighted_norm_kernel_dilate (σ : 𝓢(E,ℂ))
    (r : ℝ) (hr : 0 < r) (a R : ℝ) (m : ℕ) :
    (∫ y, ‖kernel (dilateSymbol σ r hr) y‖ * ‖y‖^a * (1+R+‖y‖)^m) =
      (r^a)⁻¹ * ∫ y, ‖kernel σ y‖ * ‖y‖^a * (1+R+‖r⁻¹ • y‖)^m := by
  have positive : 0 < r^a := Real.rpow_pos_of_pos hr _
  have scale (y : E) :
      ‖kernel (dilateSymbol σ r hr) y‖ * ‖y‖^a * (1+R+‖y‖)^m =
      (r^Module.finrank ℝ E) * (r^a)⁻¹ *
        (‖kernel σ (r • y)‖ * ‖r • y‖^a * (1+R+‖r⁻¹ • (r • y)‖)^m) := by
    rw [inv_smul_smul₀ hr.ne', kernel_dilateSymbol, norm_smul,
      Real.norm_eq_abs, abs_of_pos (pow_pos hr _), norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg _)]
    field_simp
  simp_rw [scale]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume
      (fun y : E => ‖kernel σ y‖ * ‖y‖^a * (1+R+‖r⁻¹ • y‖)^m) r (hR := hr.le), smul_eq_mul]
  have dim : r^Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp

theorem weighted_norm_kernel_dilate_le (σ : 𝓢(E,ℂ))
    {r a R : ℝ} (hr : 1 ≤ r) (ha : 0 < a) (ha1 : a ≤ 1) (hR : 0 ≤ R) (m : ℕ) :
    (∫ y, ‖kernel (dilateSymbol σ r (by linarith)) y‖ * ‖y‖^a * (1+R+‖y‖)^m) ≤
      (r^a)⁻¹ * ∫ y, ‖kernel σ y‖ * ‖y‖^a * (1+R+‖y‖)^m := by
  rw [integral_weighted_norm_kernel_dilate]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun y => by positivity)
    (SchwartzHolderMoments.polynomial_integrable volume (kernel σ) ha ha1 hR m)
  filter_upwards with y
  have small : ‖r⁻¹ • y‖ ≤ ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hr)
  have polynomial : (1+R+‖r⁻¹ • y‖)^m ≤ (1+R+‖y‖)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  exact mul_le_mul_of_nonneg_left polynomial (by positivity)
end LeanShared.FourierSchwartzKernel
