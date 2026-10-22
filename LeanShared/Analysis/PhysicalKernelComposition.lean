module
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Exact physical kernel representation of a localized composition of
two convolution operators. All Fubini hypotheses are derived from the
actual compact supports of the amplitude and input core function. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.PhysicalKernelComposition
variable {E:Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem identity (μ ν:Measure E) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (G:E→E) (continuousG:Continuous G) (g u k₀ k₁:E→ℂ)
    (continuousg:Continuous g) (continuousu:Continuous u)
    (continuous₀:Continuous k₀) (continuous₁:Continuous k₁)
    (compactg:HasCompactSupport g) (compactu:HasCompactSupport u) (x:E):
    (∫w,k₀ (x-w)*g w*(∫y,k₁ (G w-y)*u y ∂ν) ∂μ)=
      ∫y,(∫w,g w*k₀ (x-w)*k₁ (G w-y) ∂μ)*u y ∂ν:=by
  let f:E→E→ℂ:=fun w y=>g w*k₀ (x-w)*k₁ (G w-y)*u y
  have continuous:Continuous f.uncurry:=by
    dsimp only [f]
    fun_prop
  have compact:HasCompactSupport f.uncurry:=by
    apply HasCompactSupport.intro (compactg.prod compactu)
    intro p outside
    by_cases hg:p.1∈tsupport g
    · have hu:p.2∉tsupport u:=fun hu=>outside ⟨hg,hu⟩
      dsimp only [Function.uncurry,f]
      rw [image_eq_zero_of_notMem_tsupport hu,mul_zero]
    · dsimp only [Function.uncurry,f]
      rw [image_eq_zero_of_notMem_tsupport hg,zero_mul,zero_mul,zero_mul]
  calc
    _=∫w,(∫y,f w y ∂ν) ∂μ:=by
      apply integral_congr_ae
      filter_upwards with w
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [f]
      ring
    _=∫y,(∫w,f w y ∂μ) ∂ν:=integral_integral_swap_of_hasCompactSupport continuous compact
    _=_:=by
      apply integral_congr_ae
      filter_upwards with y
      rw [←integral_mul_const]
end LeanShared.PhysicalKernelComposition
