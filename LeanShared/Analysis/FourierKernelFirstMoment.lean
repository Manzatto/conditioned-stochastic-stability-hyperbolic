module
public import LeanShared.Analysis.FourierKernelIntegral
public import LeanShared.Analysis.SchwartzHolderMoments
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Actual first moments of the inverse Fourier kernel vanish when the
actual multiplier derivative vanishes at zero. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.FourierSchwartzKernel
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbol_fderiv_zero (σ:𝓢(E,ℂ))
    (zero:∀ᶠ ξ in 𝓝 (0:E),σ ξ=0) :
    fderiv ℝ (fun ξ=>ConeFourierBlocks.mathlibSymbol σ ξ) 0=0 := by
  have continuous : Continuous (fun ξ:E=>(2*Real.pi:ℝ) • ξ) := continuous_id.const_smul _
  have scale : Tendsto (fun ξ:E=>(2*Real.pi:ℝ) • ξ) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using continuous.tendsto (0:E)
  have equal : (fun ξ=>ConeFourierBlocks.mathlibSymbol σ ξ)=ᶠ[𝓝 (0:E)] (fun _=>0) := by
    filter_upwards [scale.eventually zero] with ξ hξ
    simpa only [ConeFourierBlocks.mathlibSymbol_apply] using hξ
  rw [equal.fderiv_eq]
  exact fderiv_const_apply (0:ℂ)

set_option backward.isDefEq.respectTransparency false in
theorem first_moment (σ:𝓢(E,ℂ))
    (zero:fderiv ℝ (fun ξ=>ConeFourierBlocks.mathlibSymbol σ ξ) 0=0) (v:E) :
    (∫ y, (inner ℝ y v:ℂ)*kernel σ y)=0 := by
  borelize E
  have moment : Integrable (fun y=>‖y‖*‖kernel σ y‖) := by
    simpa only [pow_one] using (kernel σ).integrable_pow_mul volume 1
  let g := VectorFourier.fourierSMulRight (innerSL ℝ) (fun y=>kernel σ y)
  have gi : Integrable g := by
    apply (moment.const_mul (2*Real.pi*‖innerSL ℝ (E:=E)‖)).mono'
    · exact (kernel σ).continuous.aestronglyMeasurable.fourierSMulRight
    · filter_upwards with y
      simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le
        (innerSL ℝ) (fun z=>kernel σ z) y
  have transform : 𝓕 (fun y=>kernel σ y) = fun ξ=>ConeFourierBlocks.mathlibSymbol σ ξ := by
    simpa only [SchwartzMap.fourier_coe] using
      congrArg (fun q:𝓢(E,ℂ)=>(q:E→ℂ)) (ConeFourierBlocks.fourier_kernel σ)
  have derivative := (Real.hasFDerivAt_fourier (kernel σ).integrable moment (0:E)).fderiv
  rw [transform,zero] at derivative
  have scalar := congrArg (fun A:E→L[ℝ]ℂ=>A v) derivative
  rw [Real.fourier_continuousLinearMap_apply gi] at scalar
  simp only [zero_apply,Real.fourier_eq,inner_zero_right,neg_zero,
    Real.fourierChar.map_zero_eq_one,one_smul] at scalar
  have integrand : (fun y=>VectorFourier.fourierSMulRight (innerSL ℝ) (fun z=>kernel σ z) y v)=
      fun y=> (-(2*Real.pi*Complex.I))*((inner ℝ y v:ℂ)*kernel σ y) := by
    funext y
    simp only [VectorFourier.fourierSMulRight_apply,innerSL_apply_apply ℝ,RCLike.real_smul_eq_coe_mul,smul_eq_mul]
    with_unfolding_all rfl
  change (0:ℂ)=(∫ y,VectorFourier.fourierSMulRight (innerSL ℝ) (fun z=>kernel σ z) y v) at scalar
  rw [integrand,integral_const_mul] at scalar
  have nonzero : (-(2*Real.pi*Complex.I):ℂ)≠0 := by
    simp [Real.pi_ne_zero]
  exact (mul_eq_zero.mp scalar.symm).resolve_left nonzero
end LeanShared.FourierSchwartzKernel
