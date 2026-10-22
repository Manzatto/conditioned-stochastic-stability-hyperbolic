module
public import LeanShared.Analysis.FourierKernelHolderDilation
public import LeanShared.Analysis.SchwartzWeightedRealMoment
public import LeanShared.Analysis.FourierWeightedMomentDilation

/-! The radial-envelope moment of an actual dilated Fourier kernel gains r^-a. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_norm_kernel_dilate_le_any (σ : 𝓢(E,ℂ))
    {r a R : ℝ} (hr : 1 ≤ r) (ha : 0 ≤ a) (hR : 0 ≤ R) (m : ℕ) :
    (∫ y, ‖kernel (dilateSymbol σ r (by linarith)) y‖ * ‖y‖^a * (1+R+‖y‖)^m) ≤
      (r^a)⁻¹ * ∫ y, ‖kernel σ y‖ * ‖y‖^a * (1+R+‖y‖)^m := by
  rw [integral_weighted_norm_kernel_dilate]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_of_nonneg (ae_of_all _ fun y => by positivity)
    (SchwartzHolderMoments.polynomial_integrable_any volume (kernel σ) ha hR m)
  filter_upwards with y
  have small : ‖r⁻¹ • y‖ ≤ ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hr)
  have polynomial : (1+R+‖r⁻¹ • y‖)^m ≤ (1+R+‖y‖)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  exact mul_le_mul_of_nonneg_left polynomial (by positivity)
end LeanShared.FourierSchwartzKernel
