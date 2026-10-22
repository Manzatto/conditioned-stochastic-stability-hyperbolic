module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! The intrinsic model's generator identity determines its actual KL
operator, independently of measurability and norm-bound proof choices. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [MeasurableSpace Ω]

omit [CompleteSpace E] in
/-- This is the exact normalized-average identity needed by the concrete
manifold supported-core source constructor. -/
theorem ActualAnnealedInputs.operator_eq_actual_average
    {law : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : E →L[ℂ] W} {scale : ℝ} (inputs : ActualAnnealedInputs law hprob i scale)
    (ε : ℝ≥0) (A : Ω → E →L[ℂ] E)
    (hmeas : ∀ f, AEStronglyMeasurable (fun z => A z f) (law ε))
    (L : ℝ) (hbound : ∀ z, ‖A z‖ ≤ L)
    (hgenerator : ∀ z, inputs.generator ε z = A z) :
    inputs.operator ε = (((scale⁻¹ : ℝ) : ℂ) •
      LeanShared.AnnealedOperatorBounds.pointwiseAnnealed (law ε) A hmeas L hbound) := by
  let _ := hprob ε
  apply ContinuousLinearMap.ext
  intro v
  change (((scale⁻¹ : ℝ) : ℂ) • ∫ z, inputs.generator ε z v ∂law ε) =
    (((scale⁻¹ : ℝ) : ℂ) • ∫ z, A z v ∂law ε)
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => congrArg (fun T : E →L[ℂ] E => T v) (hgenerator z)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
