module
public import LeanShared.Analysis.ActualGradientResidualEnvelope
public import LeanShared.Analysis.CompatiblePhysicalDerivative
import Mathlib.Tactic

/-! Both actual directional terms in the centered regularized kernel
have uniform sharp product envelopes. Differentiation is physical and
frequency compatibility comes from the same Banach-valued convolution. -/
public noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction
namespace LeanShared.UniformDirectionalKernelEnvelope
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
      ∀x y w:E,∀scale₁ scale₂:ℝ,
        (‖𝓕 (fun ζ=>fderiv ℝ
          (fun w'=>SupportedJetFourierEvaluation.physical (2*m) K (qr w') ζ) w v)
          (encode (scale₁ • (x-w)) (scale₂ • (G p w-y)))‖≤
          C₁*(r*(r^α)⁻¹)*envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G p w-y))) ∧
        ‖𝓕 (fun ζ=>(fderiv ℝ (NonlinearFourierPhaseGradient.phase (G p)
          (s p • (decode ζ).1) (t p • (decode ζ).2)) w v:ℂ)*
          SupportedJetFourierEvaluation.physical (2*m) K (q p w-qr w) ζ)
          (encode (scale₁ • (x-w)) (scale₂ • (G p w-y)))‖≤
          C₀*(r^α)⁻¹*envelope m (scale₁ • (x-w))*envelope m (scale₂ • (G p w-y)):=by
  obtain ⟨C,hC,residual⟩:=ActualGradientResidualEnvelope.exists_bound hD v m compactK
  let M₀:ℝ:=∫y,‖κ y‖*‖y‖^α ∂μ
  let M₁:ℝ:=∫y,‖fderiv ℝ κ y‖*‖y‖^α ∂μ
  have hm₀:0≤M₀:=integral_nonneg (fun _=>by positivity)
  have hm₁:0≤M₁:=integral_nonneg (fun _=>by positivity)
  let A:ℝ:=4^(2*m)*((2*m+1:ℕ)*volume.real K)
  have hA:0≤A:=by dsimp [A];positivity
  refine ⟨A*H*M₁*‖v‖,C*H*M₀,by positivity,by positivity,?_⟩
  intro p r hr qr x y w scale₁ scale₂
  constructor
  · have regular:ContDiff ℝ 1 qr:=
      (BanachNormalizedKernelDilation.compact compactκ hr).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (BanachNormalizedKernelDilation.smooth smoothκ r)
        ((q p).continuous.locallyIntegrable (μ:=μ))
    let z:=encode (scale₁ • (x-w)) (scale₂ • (G p w-y))
    let ev:SupportedFiniteJetSpace.space (2*m) K→L[ℝ]ℂ:=
      (SupportedJetFourierEvaluation.evaluation (2*m) compactK z).restrictScalars ℝ
    have equation:fderiv ℝ (fun w'=>ev (qr w')) w v=ev (fderiv ℝ qr w v):=
      congrArg (fun L:E→L[ℝ]ℂ=>L v)
        (ev.hasFDerivAt.comp w ((regular.differentiable (by norm_num) w).hasFDerivAt)).fderiv
    obtain ⟨_,_,derivative⟩:=SupportedJetRegularizedKernel.controls μ (2*m) compactK
      smoothκ compactκ mass (q p) hα hH (holder p) hr
    have raw:=derivative w z v
    change (1+‖z‖)^(2*m)*‖fderiv ℝ (fun w'=>ev (qr w')) w v‖≤_ at raw
    rw [equation] at raw
    have fourierEq:𝓕 (fun ζ=>fderiv ℝ
        (fun w'=>SupportedJetFourierEvaluation.physical (2*m) K (qr w') ζ) w v) z=
        ev (fderiv ℝ qr w v):=by
      simp_rw [CompatiblePhysicalDerivative.formula (2*m) K regular]
      exact (SupportedJetFourierEvaluation.evaluation_eq (2*m) compactK z _).symm
    rw [fourierEq]
    exact (HilbertFrequencyPair.product_decay raw).trans_eq (by
      dsimp only [z]
      simp only [decode_encode]
      dsimp [A,M₁]
      ring)
  · have raw:=residual μ κ smoothκ compactκ mass (q p) α H r hα hH (holder p) hr
      (G p) (smoothG p) (gv p) (s p) (t p) (hs p) (ht p) x y w scale₁ scale₂
    exact raw.trans_eq (by dsimp [M₀];ring)
end LeanShared.UniformDirectionalKernelEnvelope
