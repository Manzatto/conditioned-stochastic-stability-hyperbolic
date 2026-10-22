module
public import LeanShared.Analysis.HilbertProductFourier
public import LeanShared.Analysis.FourierSchwartzKernel
public import LeanShared.Analysis.CompactFourierFubini
public import LeanShared.Analysis.NormalizedCenteredFrequency
import Mathlib.Tactic

/-! The exact two physical convolution kernels are the actual joint
frequency-cutoff kernel, including the manuscript's normalization. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap
namespace LeanShared.PhysicalTwoKernelIdentity
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem kernel_eq_fourier (σ:𝓢(E,ℂ)) (x:E):
    FourierSchwartzKernel.kernel σ x=(FourierSchwartzKernel.normalization (E:=E):ℂ)*
      𝓕 (fun ξ=>σ ξ) (-(2*Real.pi)⁻¹ • x):=by
  rw [FourierSchwartzKernel.kernel_apply,←CompactFourierFubini.exponential_eq_fourier]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  rw [real_inner_comm]

theorem product_identity (σ τ:𝓢(E,ℂ)) (x y:E):
    (FourierSchwartzKernel.normalization (E:=E):ℂ)^2*
      𝓕 (fun ζ:Space E=>σ (decode ζ).1*τ (decode ζ).2) (-(2*Real.pi)⁻¹ • encode x y)=
      FourierSchwartzKernel.kernel σ x*FourierSchwartzKernel.kernel τ y:=by
  rw [NormalizedCenteredFrequency.smul_encode,HilbertProductFourier.fourier_product,
    kernel_eq_fourier,kernel_eq_fourier]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem product_compact (σ τ:𝓢(E,ℂ)) (hs:HasCompactSupport σ) (ht:HasCompactSupport τ):
    HasCompactSupport (fun ζ:Space E=>σ (decode ζ).1*τ (decode ζ).2):=by
  have hc:HasCompactSupport (fun uv:E × E=>σ uv.1*τ uv.2):=by
    apply HasCompactSupport.intro (hs.prod ht)
    intro uv huv
    by_cases hu:uv.1∈tsupport σ
    · have hv:uv.2∉tsupport τ:=fun hv=>huv ⟨hu,hv⟩
      rw [image_eq_zero_of_notMem_tsupport hv,mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hu,zero_mul]
  exact hc.comp_homeomorph (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem product_smooth (σ τ:𝓢(E,ℂ)):
    ContDiff ℝ ∞ (fun ζ:Space E=>σ (decode ζ).1*τ (decode ζ).2):=
  ((σ.smooth ⊤).comp (decode (E:=E)).contDiff.fst).mul
    ((τ.smooth ⊤).comp (decode (E:=E)).contDiff.snd)
end LeanShared.PhysicalTwoKernelIdentity
