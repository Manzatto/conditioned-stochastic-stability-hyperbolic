module
public import LeanShared.Analysis.ConeFourierBlocks

/-! The actual inverse Fourier kernel's integral is the literal
multiplier value at zero. Thus a high-frequency symbol vanishing at zero
has zero mean; this is proved with the manuscript's normalization. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace LeanShared.FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_kernel (σ : 𝓢(E,ℂ)) : (∫ y, kernel σ y) = σ 0 := by
  have transform := congrArg (fun f : 𝓢(E,ℂ) => f 0) (ConeFourierBlocks.fourier_kernel σ)
  simpa only [SchwartzMap.fourier_coe, Real.fourier_eq, inner_zero_right, neg_zero,
    Real.fourierChar.map_zero_eq_one, one_smul, ConeFourierBlocks.mathlibSymbol_apply, smul_zero] using transform

theorem integral_kernel_zero (σ : 𝓢(E,ℂ)) (zero : σ 0 = 0) : (∫ y, kernel σ y) = 0 :=
  (integral_kernel σ).trans zero
end LeanShared.FourierSchwartzKernel
