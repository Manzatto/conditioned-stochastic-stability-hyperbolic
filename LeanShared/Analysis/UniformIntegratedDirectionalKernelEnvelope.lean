module
public import LeanShared.Analysis.UniformDirectionalKernelEnvelope
public import LeanShared.Analysis.CenteredProductIntegral
public import LeanShared.Analysis.NormalizedCenteredFrequency
import Mathlib.Tactic

/-! The sharp actual directional envelopes integrate to the same
centered physical convolution majorant, with exact Fourier normalization. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction
namespace LeanShared.UniformIntegratedDirectionalKernelEnvelope
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem exists_bounds {P:Type*} (μ:Measure E) [μ.IsAddHaarMeasure] (m:ℕ)
    {K:Set (Space E)} (compactK:IsCompact K)
    {κ:E→ℝ} (smoothκ:ContDiff ℝ 1 κ) (compactκ:HasCompactSupport κ)
    (mass:∫y,κ y ∂μ=1) (q:P→E→ᵇ(SupportedFiniteJetSpace.space (2*m) K))
    {α H D:ℝ} (hα:0<α) (hH:0≤H) (hD:0≤D)
    (holder:∀p x y,‖q p x-q p y‖≤H*‖x-y‖^α)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p)) (gv:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1) (v:E):
    ∃C₁ C₀:ℝ,0≤C₁ ∧0≤C₀ ∧∀p,∀r:ℝ,0<r→
      let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q p y)
      ∀L:Set E,IsCompact L→∀x y:E,∀a b:ℝ,
        let J:=∫w in L,envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
          envelope m (((2*Real.pi)⁻¹*b) • (G p w-y)) ∂μ
        (‖∫w in L,𝓕 (fun ζ=>fderiv ℝ
          (fun w'=>SupportedJetFourierEvaluation.physical (2*m) K (qr w') ζ) w v)
          (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G p w-y))) ∂μ‖≤C₁*(r*(r^α)⁻¹)*J) ∧
        ‖∫w in L,𝓕 (fun ζ=>(fderiv ℝ (NonlinearFourierPhaseGradient.phase (G p)
          (s p • (decode ζ).1) (t p • (decode ζ).2)) w v:ℂ)*
          SupportedJetFourierEvaluation.physical (2*m) K (q p w-qr w) ζ)
          (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G p w-y))) ∂μ‖≤C₀*(r^α)⁻¹*J:=by
  obtain ⟨C₁,C₀,hC₁,hC₀,bound⟩:=UniformDirectionalKernelEnvelope.exists_bounds
    μ m compactK smoothκ compactκ mass q hα hH hD holder G smoothG gv s t hs ht v
  refine ⟨C₁,C₀,hC₁,hC₀,?_⟩
  intro p r hr qr L compactL x y a b J
  have estimates (w:E):=bound p r hr x y w (-(2*Real.pi)⁻¹*a) (-(2*Real.pi)⁻¹*b)
  constructor
  · apply CenteredProductIntegral.bound μ compactL m (G p) (smoothG p).continuous x y
      ((2*Real.pi)⁻¹*a) ((2*Real.pi)⁻¹*b) (C₁*(r*(r^α)⁻¹))
    intro w _
    simpa only [←NormalizedCenteredFrequency.center,NormalizedCenteredFrequency.envelope_sign] using (estimates w).1
  · apply CenteredProductIntegral.bound μ compactL m (G p) (smoothG p).continuous x y
      ((2*Real.pi)⁻¹*a) ((2*Real.pi)⁻¹*b) (C₀*(r^α)⁻¹)
    intro w _
    simpa only [←NormalizedCenteredFrequency.center,NormalizedCenteredFrequency.envelope_sign] using (estimates w).2
end LeanShared.UniformIntegratedDirectionalKernelEnvelope
