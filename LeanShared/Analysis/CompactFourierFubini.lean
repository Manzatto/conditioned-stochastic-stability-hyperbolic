module
public import LeanShared.Analysis.SupportedJetFourierEvaluation
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Compactly supported continuous kernels admit Fourier inversion of
the physical integral without an additional Fubini/integrability input.+The sign and the factor 2π are those of Mathlib's actual Fourier transform. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform
namespace LeanShared.CompactFourierFubini
variable {X:Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

theorem fourier_integral (μ:Measure X) [IsFiniteMeasureOnCompacts μ]
    {f:X→Z→ℂ} (hc:Continuous f.uncurry) (hs:HasCompactSupport f.uncurry) (z:Z):
    𝓕 (fun ζ=>∫w,f w ζ ∂μ) z=∫w,𝓕 (f w) z ∂μ:=by
  let a:Z→ℂ:=SupportedJetFourierEvaluation.weight z
  have ca:Continuous a:=by change Continuous (fun w:Z=>Complex.exp ((-2*Real.pi*inner ℝ w z:ℝ)*Complex.I)); fun_prop
  have cont:Continuous (fun p:X × Z=>a p.2*f p.1 p.2):=
    (ca.comp continuous_snd).mul hc
  have compact:HasCompactSupport (fun p:X × Z=>a p.2*f p.1 p.2):=hs.mul_left
  simp only [Real.fourier_eq',smul_eq_mul]
  change (∫ζ,a ζ*(∫w,f w ζ ∂μ))=∫w,(∫ζ:Z,a ζ*f w ζ) ∂μ
  simp_rw [←integral_const_mul]
  exact (integral_integral_swap_of_hasCompactSupport cont compact).symm

theorem exponential_integral (μ:Measure X) [IsFiniteMeasureOnCompacts μ]
    {f:X→Z→ℂ} (hc:Continuous f.uncurry) (hs:HasCompactSupport f.uncurry) (z:Z):
    (∫ζ,Complex.exp (Complex.I*(inner ℝ ζ z:ℂ))*(∫w,f w ζ ∂μ))=
      ∫w,(∫ζ:Z,Complex.exp (Complex.I*(inner ℝ ζ z:ℂ))*f w ζ) ∂μ:=by
  have ca:Continuous (fun ζ:Z=>Complex.exp (Complex.I*(inner ℝ ζ z:ℂ))):=by fun_prop
  have cont:Continuous (fun p:X × Z=>Complex.exp (Complex.I*(inner ℝ p.2 z:ℂ))*f p.1 p.2):=
    (ca.comp continuous_snd).mul hc
  simp_rw [←integral_const_mul]
  exact (integral_integral_swap_of_hasCompactSupport cont hs.mul_left).symm

theorem exponential_eq_fourier (f:Z→ℂ) (z:Z):
    (∫ζ,Complex.exp (Complex.I*(inner ℝ ζ z:ℂ))*f ζ)=
      𝓕 f (-(2*Real.pi)⁻¹ • z):=by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with ζ
  simp only [smul_eq_mul,inner_smul_right]
  congr 2
  have hpi:2*Real.pi≠0:=mul_ne_zero (by norm_num) Real.pi_ne_zero
  have eqn:-2*Real.pi*(-(2*Real.pi)⁻¹*inner ℝ ζ z)=inner ℝ ζ z:=by
    field_simp
  rw [eqn]
  ring
end LeanShared.CompactFourierFubini
