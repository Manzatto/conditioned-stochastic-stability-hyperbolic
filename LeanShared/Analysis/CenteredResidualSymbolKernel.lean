module
public import LeanShared.Analysis.CompactSymbolMultiplierEnvelope
public import LeanShared.Analysis.CenteredRegularizedSymbolKernel
import Mathlib.Tactic

/-! The residual phase-gradient multiplier preserves the centered
product envelope, with the sharp Holder regularization gain. Constants
are uniform over a compact parameter set and are constructed from the
actual smooth multiplier. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction
namespace LeanShared.CenteredResidualSymbolKernel
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]
  {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_controls (ψ:V × Space E→ℂ) (smoothψ:ContDiff ℝ ∞ ψ)
    {P:Set V} (compactP:IsCompact P) (m:ℕ)
    {K:Set (Space E)} (compactK:IsCompact K):
    ∃C:ℝ,0≤C ∧∀(μ:Measure E) [μ.IsAddHaarMeasure],
      ∀κ:E→ℝ,∀_smooth:ContDiff ℝ 1 κ,∀_compact:HasCompactSupport κ,
      (∫y,κ y ∂μ)=1→∀q:E→ᵇ(SupportedFiniteJetSpace.space (2*m) K),
      ∀a H r:ℝ,0<a→0≤H→(∀x y,‖q x-q y‖≤H*‖x-y‖^a)→0<r→
      let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
      ∀p∈P,∀x y w:E,∀scale₁ scale₂:ℝ,∀G:E→E,
        ‖𝓕 (fun ζ=>ψ (p,ζ)*SupportedJetFourierEvaluation.physical (2*m) K (qr w-q w) ζ)
          (encode (scale₁ • (x-w)) (scale₂ • (G w-y)))‖≤
        (C*(H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ)))*
          envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G w-y)):=by
  obtain ⟨C,hC,bound⟩:=CompactSymbolMultiplierEnvelope.exists_bound ψ smoothψ compactP compactK (2*m)
  refine ⟨C,hC,?_⟩
  intro μ _ κ smooth compact mass q a H r ha hH holder hr qr p hp x y w scale₁ scale₂ G
  have error:=BanachScaledHolderMollification.scaled_error μ smooth.continuous compact mass q ha hH holder hr w
  have raw:=bound p hp (qr w-q w) (encode (scale₁ • (x-w)) (scale₂ • (G w-y)))
  exact HilbertFrequencyPair.product_decay (raw.trans (mul_le_mul_of_nonneg_left error hC))
end LeanShared.CenteredResidualSymbolKernel
