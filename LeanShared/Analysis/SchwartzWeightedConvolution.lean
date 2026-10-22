module
public import LeanShared.Analysis.FourierWeightedRealMomentDilation
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.ObliqueSchwartzDecay
import Mathlib.Tactic.Ring

/-! Uniform polynomially weighted bounds for actual dilated convolution,
proved from Schwartz moments and the elementary submultiplicative weight. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap Convolution
namespace LeanShared.SchwartzWeightedConvolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem block_integral (σ f : 𝓢(E,ℂ)) (x : E) :
    ConeFourierBlocks.block σ f x = ∫ y, FourierSchwartzKernel.kernel σ y*f (x-y) := by
  rw [ConeFourierBlocks.block,SchwartzMap.convolution_apply,convolution_def]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pointwise (f : 𝓢(E,ℂ)) (m : ℕ) (x y : E) :
    (1+‖x‖)^m*‖f (x-y)‖ ≤
      2^m*ObliqueSchwartzDecay.seminorm m f*(1+‖y‖)^m := by
  have triangle := norm_add_le y (x-y)
  rw [add_sub_cancel] at triangle
  have base : 1+‖x‖ ≤ (1+‖y‖)*(1+‖x-y‖) := by
    nlinarith [norm_nonneg y,norm_nonneg (x-y)]
  have polynomial : (1+‖x-y‖)^m*‖f (x-y)‖ ≤
      2^m*ObliqueSchwartzDecay.seminorm m f := by
    simpa only [ObliqueSchwartzDecay.seminorm,norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℂ) (m:=(m,0))
        (k:=m) (n:=0) le_rfl le_rfl f (x-y)
  calc
    _ ≤ ((1+‖y‖)*(1+‖x-y‖))^m*‖f (x-y)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) base m) (norm_nonneg _)
    _ = (1+‖y‖)^m*((1+‖x-y‖)^m*‖f (x-y)‖) := by rw [mul_pow,mul_assoc]
    _ ≤ (1+‖y‖)^m*(2^m*ObliqueSchwartzDecay.seminorm m f) :=
      mul_le_mul_of_nonneg_left polynomial (by positivity)
    _ = _ := mul_comm _ _

theorem bound (σ f : 𝓢(E,ℂ)) (m : ℕ) (x : E) :
    (1+‖x‖)^m*‖ConeFourierBlocks.block σ f x‖ ≤
      (2^m*ObliqueSchwartzDecay.seminorm m f)*
        ∫ y, ‖FourierSchwartzKernel.kernel σ y‖*(1+‖y‖)^m := by
  let k := FourierSchwartzKernel.kernel σ
  have moment : Integrable (fun y=>‖k y‖*(1+‖y‖)^m) := by
    simpa only [Real.rpow_zero,mul_one,add_zero] using
      SchwartzHolderMoments.polynomial_integrable_any volume k (a:=0) (R:=0) le_rfl le_rfl m
  rw [block_integral]
  calc
    _ ≤ (1+‖x‖)^m*∫ y, ‖k y*f (x-y)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ y, (1+‖x‖)^m*‖k y*f (x-y)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ y, (2^m*ObliqueSchwartzDecay.seminorm m f)*(‖k y‖*(1+‖y‖)^m) :=
      integral_mono_of_nonneg (ae_of_all _ fun y=>by positivity) (moment.const_mul _)
        (ae_of_all _ fun y=>by
          have estimate := mul_le_mul_of_nonneg_left (pointwise f m x y) (norm_nonneg (k y))
          dsimp only
          rw [norm_mul]
          nlinarith only [estimate])
    _ = _ := integral_const_mul _ _

theorem dilated_bound (σ f : 𝓢(E,ℂ)) (m : ℕ) {r : ℝ} (hr : 1 ≤ r) (x : E) :
    (1+‖x‖)^m*‖ConeFourierBlocks.block
      (FourierSchwartzKernel.dilateSymbol σ r (by linarith)) f x‖ ≤
      (2^m*ObliqueSchwartzDecay.seminorm m f)*
        ∫ y, ‖FourierSchwartzKernel.kernel σ y‖*(1+‖y‖)^m := by
  apply (bound _ f m x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Real.rpow_zero,inv_one,mul_one,one_mul,add_zero] using
    FourierSchwartzKernel.weighted_norm_kernel_dilate_le_any σ hr (a:=0) (R:=0) le_rfl le_rfl m
end LeanShared.SchwartzWeightedConvolution
