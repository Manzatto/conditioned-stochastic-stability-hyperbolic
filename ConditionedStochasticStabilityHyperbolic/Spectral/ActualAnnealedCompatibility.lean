module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedOperatorIdentity

/-! Compatibility of actual generators passes to their actual varying-law
averages. No compatibility of completed averaged operators is assumed. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.AnnealedOperatorBounds

variable {S H W V Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace Ω]

theorem ActualAnnealedInputs.operator_compatibility_of_generators
    {law : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (law ε)}
    {a : S →L[ℂ] W} {b : H →L[ℂ] V} {scale : ℝ}
    (s : ActualAnnealedInputs law hprob a scale)
    (h : ActualAnnealedInputs law hprob b scale)
    (i : S →L[ℂ] H) (ε : ℝ≥0)
    (hgenerator : ∀ z, i.comp (s.generator ε z) = (h.generator ε z).comp i) :
    i.comp (s.operator ε) = (h.operator ε).comp i := by
  let _ := hprob ε
  have hc := pointwiseAnnealed_compatibility (law ε) (s.generator ε)
    (s.measurable ε) s.operatorBound (s.generator_bound ε)
    (h.generator ε) (h.measurable ε) h.operatorBound (h.generator_bound ε)
    i (fun z x => congrArg (fun L : S →L[ℂ] H => L x) (hgenerator z))
  ext x
  have hx := congrArg (fun L : S →L[ℂ] H => L x) hc
  change i ((((scale⁻¹ : ℝ) : ℂ) •
    pointwiseAnnealed (law ε) (s.generator ε) (s.measurable ε)
      s.operatorBound (s.generator_bound ε)) x) =
    ((((scale⁻¹ : ℝ) : ℂ) • pointwiseAnnealed (law ε) (h.generator ε)
      (h.measurable ε) h.operatorBound (h.generator_bound ε)) (i x))
  simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
    using congrArg ((((scale⁻¹ : ℝ) : ℂ)) • ·) hx

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
