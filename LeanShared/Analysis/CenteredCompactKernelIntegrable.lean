module
public import LeanShared.Analysis.NonlinearKernelCentering
public import LeanShared.Analysis.CompactFourierFiniteSum
import Mathlib.Tactic

/-! Actual centered Fourier kernels and finite sums are integrable in
the physical variable, derived from joint compact support. -/
public noncomputable section
open Set MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace LeanShared.CenteredCompactKernelIntegrable
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem integrable (μ:Measure E) [IsFiniteMeasureOnCompacts μ]
    (G:E→E) (gc:Continuous G) (a b:ℝ) (x y:E)
    (h:E→Space E→ℂ) (hc:Continuous h.uncurry) (hs:HasCompactSupport h.uncurry):
    Integrable (fun w=>𝓕 (h w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y)))) μ:=by
  let k:E × Space E→ℂ:=fun p=>Complex.exp
    (Complex.I*(inner ℝ p.2 (encode (a • (x-p.1)) (b • (G p.1-y))):ℂ))*h p.1 p.2
  have cc:Continuous (fun w:E=>encode (a • (x-w)) (b • (G w-y))):=by
    change Continuous (fun w=>WithLp.toLp 2 (a • (x-w),b • (G w-y)))
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous.comp
      ((continuous_const.smul (continuous_const.sub continuous_id)).prodMk
        (continuous_const.smul (gc.sub continuous_const)))
  have ck:Continuous k:=((Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_snd.inner (cc.comp continuous_fst))))).mul hc)
  have sk:HasCompactSupport k:=hs.mul_left
  have int:Integrable k (μ.prod volume):=ck.integrable_of_hasCompactSupport sk
  have raw:=int.integral_prod_left
  convert! raw using 1
  funext w
  exact (NonlinearKernelCentering.centered_fourier G a b x y w (h w)).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)] in
theorem compact_frequency_section {h:E→Space E→ℂ}
    (hs:HasCompactSupport h.uncurry) (w:E):HasCompactSupport (h w):=by
  apply HasCompactSupport.intro (hs.image continuous_snd)
  intro ζ hζ
  by_contra hn
  exact hζ (mem_image_of_mem Prod.snd
    (subset_tsupport h.uncurry (show (w,ζ)∈Function.support h.uncurry from hn)))

theorem integral_fourier_sum {ι:Type*} [Fintype ι]
    (μ:Measure E) [IsFiniteMeasureOnCompacts μ]
    (G:E→E) (gc:Continuous G) (a b:ℝ) (x y:E)
    (h:ι→E→Space E→ℂ) (hc:∀i,Continuous (h i).uncurry)
    (hs:∀i,HasCompactSupport (h i).uncurry):
    (∫w,𝓕 (fun ζ=>∑i,h i w ζ) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ)=
      ∑i,∫w,𝓕 (h i w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G w-y))) ∂μ:=by
  have eqn (w:E):𝓕 (fun ζ=>∑i,h i w ζ)=fun z=>∑i,𝓕 (h i w) z:=by
    funext z
    exact CompactFourierFiniteSum.fourier_sum (fun i=>h i w)
      (fun i=>(hc i).comp (continuous_const.prodMk continuous_id))
      (fun i=>compact_frequency_section (hs i) w) z
  simp_rw [eqn]
  exact integral_finsetSum _ (fun i _=>integrable μ G gc a b x y (h i) (hc i) (hs i))
end LeanShared.CenteredCompactKernelIntegrable
