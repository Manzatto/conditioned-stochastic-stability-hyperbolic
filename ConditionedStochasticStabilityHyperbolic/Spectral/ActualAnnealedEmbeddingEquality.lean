module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! The proved inclusion-tower identity identifies the actual KL input types.
This transports no estimates beyond equality and preserves the actual operators. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {S W Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [MeasurableSpace Ω]

@[expose] def ActualAnnealedInputs.changeEmbedding
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (j : S →L[ℂ] W) (h : i = j) : ActualAnnealedInputs law probability j R := h ▸ s

omit [CompleteSpace S] [CompleteSpace W] in
@[simp] theorem ActualAnnealedInputs.changeEmbedding_generator
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (j : S →L[ℂ] W) (h : i = j) :
    (s.changeEmbedding j h).generator = s.generator := by
  subst j
  rfl

omit [CompleteSpace S] [CompleteSpace W] in
@[simp] theorem ActualAnnealedInputs.changeEmbedding_operator
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (j : S →L[ℂ] W) (h : i = j) :
    (s.changeEmbedding j h).operator = s.operator := by
  subst j
  rfl

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
