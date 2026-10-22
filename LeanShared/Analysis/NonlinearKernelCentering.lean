module
public import LeanShared.Analysis.HilbertFrequencyPair
public import LeanShared.Analysis.NonstationaryPhaseIntegration
public import LeanShared.Analysis.CompactFourierFubini
import Mathlib.Tactic

/-! The exact nonlinear Fourier kernel center, with its actual Hilbert
frequency variables, signs, physical scales and Fourier normalization. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace LeanShared.NonlinearKernelCentering
open HilbertFrequencyPair NonstationaryPhaseIntegration
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace (Space E)] [BorelSpace (Space E)]

omit [FiniteDimensional ℝ E] [MeasurableSpace (Space E)] [BorelSpace (Space E)] in
theorem inner_encode (ζ:Space E) (x y:E):
    ⟪ζ,encode x y⟫=⟪(decode ζ).1,x⟫+⟪(decode ζ).2,y⟫:=by
  rw [WithLp.prod_inner_apply]
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace (Space E)] [BorelSpace (Space E)] in
theorem phase_identity (G:E→E) (a b Λ:ℝ) (x y w:E) (ζ:Space E)
    (s t:ℝ) (ha:Λ*s=a) (hb:Λ*t=b):
    Complex.exp (Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫:ℝ):ℂ))*
      oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w=
    Complex.exp (Complex.I*(⟪ζ,encode (a • (x-w)) (b • (G w-y))⟫:ℂ)):=by
  rw [oscillation,←Complex.exp_add,inner_encode]
  simp only [inner_smul_right,inner_sub_right]
  congr 1
  have realIdentity:(a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫)+
      Λ*(-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫)=
      a*(⟪(decode ζ).1,x⟫-⟪(decode ζ).1,w⟫)+
        b*(⟪(decode ζ).2,G w⟫-⟪(decode ζ).2,y⟫):=by
    calc
      _ = a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫-
        (Λ*s)*⟪(decode ζ).1,w⟫+(Λ*t)*⟪(decode ζ).2,G w⟫:=by ring
      _ = _:=by rw [ha,hb]; ring
  calc
    _ = Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫+
      Λ*(-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫):ℝ):ℂ):=by push_cast;ring
    _ = _:=by rw [realIdentity]

theorem centered_fourier (G:E→E) (a b:ℝ) (x y w:E) (q:Space E→ℂ):
    (∫ζ,Complex.exp (Complex.I*(⟪ζ,encode (a • (x-w)) (b • (G w-y))⟫:ℂ))*q ζ)=
      𝓕 q (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))):=
  CompactFourierFubini.exponential_eq_fourier q _

variable [MeasurableSpace E] [BorelSpace E]

theorem integrable_weighted_kernel (μ:Measure E) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (G:E→E) (gc:Continuous G) (a b Λ s t:ℝ) (x y:E)
    (h:E→Space E→ℂ) (hc:Continuous h.uncurry) (hs:HasCompactSupport h.uncurry):
    Integrable (fun ζ=>Complex.exp (Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫:ℝ):ℂ))*
      (∫w,oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*h w ζ ∂μ)):=by
  let k:E × Space E→ℂ:=fun p=>
    Complex.exp (Complex.I*((a*⟪(decode p.2).1,x⟫-b*⟪(decode p.2).2,y⟫:ℝ):ℂ))*
      (oscillation Λ (fun w=>-s*⟪(decode p.2).1,w⟫+t*⟪(decode p.2).2,G w⟫) p.1*h p.1 p.2)
  have co:Continuous (fun p:E × Space E=>oscillation Λ
      (fun w=>-s*⟪(decode p.2).1,w⟫+t*⟪(decode p.2).2,G w⟫) p.1):=by
    unfold oscillation
    fun_prop
  have ce:Continuous (fun p:E × Space E=>
      Complex.exp (Complex.I*((a*⟪(decode p.2).1,x⟫-b*⟪(decode p.2).2,y⟫:ℝ):ℂ))):=by fun_prop
  have ck:Continuous k:=ce.mul (co.mul hc)
  have sk:HasCompactSupport k:=(hs.mul_left).mul_left
  have int:=(ck.integrable_of_hasCompactSupport (μ:=μ.prod volume) sk).integral_prod_right
  simpa only [k,integral_const_mul] using int

theorem kernel_eq_integral_centered_fourier (μ:Measure E) [IsFiniteMeasureOnCompacts μ]
    (G:E→E) (gc:Continuous G) (a b Λ:ℝ) (s t:ℝ) (ha:Λ*s=a) (hb:Λ*t=b)
    (x y:E) (h:E→Space E→ℂ) (hc:Continuous h.uncurry) (hs:HasCompactSupport h.uncurry):
    (∫ζ,Complex.exp (Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫:ℝ):ℂ))*
      (∫w,oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*h w ζ ∂μ))=
    ∫w,𝓕 (h w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ:=by
  let k:E→Space E→ℂ:=fun w ζ=>
    Complex.exp (Complex.I*((a*⟪(decode ζ).1,x⟫-b*⟪(decode ζ).2,y⟫:ℝ):ℂ))*
      (oscillation Λ (fun w=>-s*⟪(decode ζ).1,w⟫+t*⟪(decode ζ).2,G w⟫) w*h w ζ)
  have co:Continuous (fun p:E × Space E=>oscillation Λ
      (fun w=>-s*⟪(decode p.2).1,w⟫+t*⟪(decode p.2).2,G w⟫) p.1):=by
    unfold oscillation
    fun_prop
  have ce:Continuous (fun p:E × Space E=>
      Complex.exp (Complex.I*((a*⟪(decode p.2).1,x⟫-b*⟪(decode p.2).2,y⟫:ℝ):ℂ))):=by fun_prop
  have ck:Continuous k.uncurry:=ce.mul (co.mul hc)
  have sk:HasCompactSupport k.uncurry:=(hs.mul_left).mul_left
  simp_rw [←integral_const_mul]
  change (∫ζ,∫w,k w ζ ∂μ)=_
  rw [←integral_integral_swap_of_hasCompactSupport ck sk]
  apply integral_congr_ae
  filter_upwards with w
  rw [←centered_fourier G a b x y w (h w)]
  apply integral_congr_ae
  filter_upwards with ζ
  dsimp [k]
  rw [←mul_assoc,phase_identity G a b Λ x y w ζ s t ha hb]
  rfl
end LeanShared.NonlinearKernelCentering
