module
public import LeanShared.Analysis.NonlinearKernelCentering
import Mathlib.Tactic

/-! Exact pointwise oscillatory integration identities pass through the
actual centered Fourier kernel. Compact support supplies every Fubini
and integrability condition; the Fourier factor 2π is retained. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace LeanShared.CenteredKernelLinearIdentity
open HilbertFrequencyPair NonstationaryPhaseIntegration
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem transfer (μ:Measure E) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (G:E→E) (gc:Continuous G) (a b Λ s t:ℝ) (ha:Λ*s=a) (hb:Λ*t=b)
    (x y:E) (f h k:E→Space E→ℂ)
    (fc:Continuous f.uncurry) (fs:HasCompactSupport f.uncurry)
    (hc:Continuous h.uncurry) (hs:HasCompactSupport h.uncurry)
    (kc:Continuous k.uncurry) (ks:HasCompactSupport k.uncurry)
    (c d e:ℂ)
    (identity:∀ζ,c*(∫w,oscillation Λ
        (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*f w ζ ∂μ)=
      d*(∫w,oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*h w ζ ∂μ)+
      e*(∫w,oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*k w ζ ∂μ)):
    c*(∫w,𝓕 (f w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ)=
      d*(∫w,𝓕 (h w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ)+
      e*(∫w,𝓕 (k w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ):=by
  rw [←NonlinearKernelCentering.kernel_eq_integral_centered_fourier μ G gc a b Λ s t ha hb x y f fc fs,
    ←NonlinearKernelCentering.kernel_eq_integral_centered_fourier μ G gc a b Λ s t ha hb x y h hc hs,
    ←NonlinearKernelCentering.kernel_eq_integral_centered_fourier μ G gc a b Λ s t ha hb x y k kc ks]
  rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,
    ←integral_add ((NonlinearKernelCentering.integrable_weighted_kernel μ G gc a b Λ s t x y h hc hs).const_mul d)
      ((NonlinearKernelCentering.integrable_weighted_kernel μ G gc a b Λ s t x y k kc ks).const_mul e)]
  apply integral_congr_ae
  filter_upwards with ζ
  calc
    _ = Complex.exp (Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫:ℝ):ℂ))*
        (c*(∫w,oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*f w ζ ∂μ)):=by ring
    _ = _:=by rw [identity];ring
end LeanShared.CenteredKernelLinearIdentity
