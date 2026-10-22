module
public import LeanShared.Analysis.SupportedJetRegularizedKernel
public import LeanShared.Analysis.HilbertFrequencyPair
import Mathlib.Tactic

/-! Actual centered product envelopes of regularized coefficient kernels.
The physical derivative holds the Fourier variable fixed, exactly as in
integration by parts before Fourier inversion; it is not a total
derivative of the moving centered argument. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution BoundedContinuousFunction
namespace LeanShared.CenteredRegularizedSymbolKernel
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem controls (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ)
    {K:Set (Space E)} (compactK:IsCompact K)
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (mass:∫y,κ y ∂μ=1) (q:E→ᵇ(SupportedFiniteJetSpace.space (2*m) K))
    {a H r:ℝ} (ha:0<a) (hH:0≤H)
    (holder:∀x y,‖q x-q y‖≤H*‖x-y‖^a) (hr:0<r) (G:E→E):
    let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
    let C:ℝ:=4^(2*m)*((2*m+1:ℕ)*volume.real K)
    (∀x y w:E,∀scale₁ scale₂:ℝ,
      let z:=encode (scale₁ • (x-w)) (scale₂ • (G w-y))
      ‖SupportedJetFourierEvaluation.evaluation (2*m) compactK z (qr w)-
        SupportedJetFourierEvaluation.evaluation (2*m) compactK z (q w)‖≤
        (C*(H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ)))*
          envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G w-y))) ∧
      ∀x y w v:E,∀scale₁ scale₂:ℝ,
        let z:=encode (scale₁ • (x-w)) (scale₂ • (G w-y))
        ‖fderiv ℝ (fun w'=>SupportedJetFourierEvaluation.evaluation (2*m) compactK z (qr w')) w v‖≤
          (C*(H*(r*(r^a)⁻¹)*(∫y,‖fderiv ℝ κ y‖*‖y‖^a ∂μ))*‖v‖)*
            envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G w-y)):=by
  obtain ⟨_,error,derivative⟩:=SupportedJetRegularizedKernel.controls μ (2*m) compactK
    smooth compact mass q ha hH holder hr
  constructor
  · intro x y w scale₁ scale₂
    have raw:=HilbertFrequencyPair.product_decay (error w (encode (scale₁ • (x-w)) (scale₂ • (G w-y))))
    exact raw
  · intro x y w v scale₁ scale₂
    have raw:=HilbertFrequencyPair.product_decay
      (derivative w (encode (scale₁ • (x-w)) (scale₂ • (G w-y))) v)
    exact raw
end LeanShared.CenteredRegularizedSymbolKernel
