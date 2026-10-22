module
public import LeanShared.Analysis.CompactFourierFubini
public import LeanShared.Analysis.SupportedJetRegularizedKernel
import Mathlib.Tactic

/-! Joint continuity, joint compact support and actual Fourier Fubini
for physical representatives of the supported finite jet family. -/
public noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped FourierTransform ContDiff Convolution
namespace LeanShared.CompactJetPhysicalKernel
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem continuous_physical (n:ℕ) (K:Set Z)
    {q:E→SupportedFiniteJetSpace.space n K} (hc:Continuous q):
    Continuous (fun p:E × Z=>SupportedJetFourierEvaluation.physical n K (q p.1) p.2):=by
  exact ((SupportedJetFourierEvaluation.physical n K).continuous.comp (hc.comp continuous_fst)).eval
    continuous_snd

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem compact_physical (n:ℕ) {K:Set Z} (compactK:IsCompact K)
    {q:E→SupportedFiniteJetSpace.space n K} (hs:HasCompactSupport q):
    HasCompactSupport (fun p:E × Z=>SupportedJetFourierEvaluation.physical n K (q p.1) p.2):=by
  apply HasCompactSupport.intro (hs.prod compactK)
  intro p hp
  by_cases hx:p.1∈tsupport q
  · have hz:p.2∉K:=fun hz=>hp ⟨hx,hz⟩
    exact (q p.1).property p.2 hz
  · rw [image_eq_zero_of_notMem_tsupport hx,map_zero]
    rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem fourier_integral (μ:Measure E) [IsFiniteMeasureOnCompacts μ]
    (n:ℕ) {K:Set Z} (compactK:IsCompact K)
    {q:E→SupportedFiniteJetSpace.space n K} (hc:Continuous q) (hs:HasCompactSupport q) (z:Z):
    𝓕 (fun ζ=>∫w,SupportedJetFourierEvaluation.physical n K (q w) ζ ∂μ) z=
      ∫w,SupportedJetFourierEvaluation.evaluation n compactK z (q w) ∂μ:=by
  have eqn:=CompactFourierFubini.fourier_integral μ
    (f:=fun w ζ=>SupportedJetFourierEvaluation.physical n K (q w) ζ)
    (continuous_physical n K hc) (compact_physical n compactK hs) z
  refine eqn.trans ?_
  apply integral_congr_ae
  filter_upwards with w
  exact (SupportedJetFourierEvaluation.evaluation_eq n compactK z (q w)).symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z] in
theorem regularized_compact (μ:Measure E) [μ.IsAddHaarMeasure]
    (n:ℕ) (K:Set Z) {κ:E→ℝ} (compact:HasCompactSupport κ)
    {q:E→SupportedFiniteJetSpace.space n K} (hs:HasCompactSupport q):
    HasCompactSupport (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] q):=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) compact hs
end LeanShared.CompactJetPhysicalKernel
