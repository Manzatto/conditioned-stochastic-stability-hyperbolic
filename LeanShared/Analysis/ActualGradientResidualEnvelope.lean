module
public import LeanShared.Analysis.CenteredResidualSymbolKernel
public import LeanShared.Analysis.NonlinearJetResidualFamily
public import LeanShared.Analysis.SmoothNonstationarySymbol
import Mathlib.Tactic

/-! The literal nonlinear phase gradient is the actual residual smooth
multiplier. Its centered kernel constant is uniform over bounded physical
first jets and every pair of normalized dyadic ratios. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction
namespace LeanShared.ActualGradientResidualEnvelope
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem exists_bound {D:ℝ} (hD:0≤D) (v:E) (m:ℕ)
    {K:Set (Space E)} (compactK:IsCompact K):
    ∃C:ℝ,0≤C ∧∀(μ:Measure E) [μ.IsAddHaarMeasure],
      ∀κ:E→ℝ,∀_smooth:ContDiff ℝ 1 κ,∀_compact:HasCompactSupport κ,
      (∫y,κ y ∂μ)=1→∀q:E→ᵇ(SupportedFiniteJetSpace.space (2*m) K),
      ∀a H r:ℝ,0<a→0≤H→(∀x y,‖q x-q y‖≤H*‖x-y‖^a)→0<r→
      ∀G:E→E,ContDiff ℝ 1 G→(∀w,‖fderiv ℝ G w‖≤D)→
      ∀s t:ℝ,‖s‖≤1→‖t‖≤1→
      let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
      ∀x y w:E,∀scale₁ scale₂:ℝ,
        ‖𝓕 (fun ζ=>(fderiv ℝ (NonlinearFourierPhaseGradient.phase G
          (s • (decode ζ).1) (t • (decode ζ).2)) w v:ℂ)*
          SupportedJetFourierEvaluation.physical (2*m) K (q w-qr w) ζ)
          (encode (scale₁ • (x-w)) (scale₂ • (G w-y)))‖≤
        (C*(H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ)))*
          envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G w-y)):=by
  let V:Type:=(E→L[ℝ]E) × (ℝ × ℝ)
  let ψ:V × Space E→ℂ:=fun p=>
    (inner ℝ (SmoothNonstationarySymbol.gradient
      (p.1.1,(p.1.2.1 • (decode p.2).1,p.1.2.2 • (decode p.2).2))) v:ℂ)
  have cs:ContDiff ℝ ∞ ψ:=by
    have ca:ContDiff ℝ ∞ (fun p:V × Space E=>p.1.1):=contDiff_fst.fst
    have cz:ContDiff ℝ ∞ (fun p:V × Space E=>decode p.2):=(decode (E:=E)).contDiff.comp contDiff_snd
    exact Complex.ofRealCLM.contDiff.comp
      (((SmoothNonstationarySymbol.smooth_gradient).comp
        (ca.prodMk (((contDiff_fst.snd.fst).smul cz.fst).prodMk
          ((contDiff_fst.snd.snd).smul cz.snd)))).inner ℝ contDiff_const)
  obtain ⟨C,hC,bound⟩:=CompactSymbolMultiplierEnvelope.exists_bound ψ cs
    (isCompact_closedBall (0:V) (D+1)) compactK (2*m)
  refine ⟨C,hC,?_⟩
  intro μ _ κ smooth compact mass q a H r ha hH holder hr G gc gv s t hs ht qr x y w scale₁ scale₂
  let p:V:=(fderiv ℝ G w,(s,t))
  have hp:p∈Metric.closedBall (0:V) (D+1):=by
    rw [Metric.mem_closedBall,dist_zero_right]
    change max ‖fderiv ℝ G w‖ (max ‖s‖ ‖t‖)≤D+1
    exact max_le ((gv w).trans (le_add_of_nonneg_right zero_le_one))
      ((max_le hs ht).trans (le_add_of_nonneg_left hD))
  have error:‖q w-qr w‖≤H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ):=by
    rw [norm_sub_rev]
    exact BanachScaledHolderMollification.scaled_error μ smooth.continuous compact mass q ha hH holder hr w
  have raw:=bound p hp (q w-qr w) (encode (scale₁ • (x-w)) (scale₂ • (G w-y)))
  have reduced:=HilbertFrequencyPair.product_decay (raw.trans (mul_le_mul_of_nonneg_left error hC))
  simpa only [ψ,p,SmoothNonstationarySymbol.gradient,decode_encode,
    NonlinearFourierPhaseGradient.derivative (gc.differentiable (by norm_num) w)] using reduced
end LeanShared.ActualGradientResidualEnvelope
