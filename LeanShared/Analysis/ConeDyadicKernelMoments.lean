module
public import LeanShared.Analysis.ConeHolderAnisotropicEmbedding
public import LeanShared.Analysis.FourierKernelLinearMoment

/-! The literal manuscript high-cone symbols, at every positive dilation,
have zero mean and all first scalar moments. No cancellation source is assumed. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace LeanShared.ConeDyadicKernelMoments
open FourierSchwartzKernel ConeDyadicSymbols
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cplus Cminus)

omit [MeasurableSpace E] [BorelSpace E] in
theorem high_eventually_zero (s:Bool) :
    ∀ᶠ ξ in 𝓝 (0:E),ConeHolderAnisotropicEmbedding.highBase χ Φ s ξ=0 := by
  filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1/2)] with ξ hξ
  have small:‖ξ‖≤1/2 := (by simpa only [Metric.mem_ball,dist_zero_right] using hξ : ‖ξ‖<1/2).le
  change high χ Φ.toFun s ξ=0
  rw [high,highReal,annular_zero_near_origin χ small,mul_zero,Complex.ofReal_zero]

omit [MeasurableSpace E] [BorelSpace E] in
theorem dilate_eventually_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠ ξ in 𝓝 (0:E),σ ξ=0)
    (r:ℝ) (hr:0<r) : ∀ᶠ ξ in 𝓝 (0:E),dilateSymbol σ r hr ξ=0 := by
  have continuous:Continuous (fun ξ:E=>r⁻¹ • ξ) := continuous_id.const_smul _
  have scale:Tendsto (fun ξ:E=>r⁻¹ • ξ) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using continuous.tendsto (0:E)
  filter_upwards [scale.eventually zero] with ξ hξ
  simpa only [dilateSymbol_apply] using hξ

 theorem mean_zero (s:Bool) (r:ℝ) (hr:0<r) :
    (∫ y,kernel (dilateSymbol (ConeHolderAnisotropicEmbedding.highBase χ Φ s) r hr) y)=0 := by
  have equal:(fun ξ=>dilateSymbol (ConeHolderAnisotropicEmbedding.highBase χ Φ s) r hr ξ)=ᶠ[𝓝 (0:E)]
      (fun _=>0) := dilate_eventually_zero _ (high_eventually_zero χ Φ s) r hr
  exact integral_kernel_zero _ equal.eq_of_nhds

 theorem linear_zero (s:Bool) (r:ℝ) (hr:0<r) (ℓ:E→L[ℝ]ℂ) :
    (∫ y,kernel (dilateSymbol (ConeHolderAnisotropicEmbedding.highBase χ Φ s) r hr) y*ℓ y)=0 :=
  linear_first_moment _ (symbol_fderiv_zero _
    (dilate_eventually_zero _ (high_eventually_zero χ Φ s) r hr)) ℓ
end LeanShared.ConeDyadicKernelMoments
