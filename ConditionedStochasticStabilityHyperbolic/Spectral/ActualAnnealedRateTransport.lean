module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedEmbeddingEquality
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedWeakTransport

/-! Exact pressure/growth constants survive the proved inclusion transports.
These facts connect concrete intrinsic pressure bounds to the final KL pair. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {S W V Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [MeasurableSpace Ω]

@[simp] theorem ActualAnnealedInputs.changeEmbedding_principal
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (j : S →L[ℂ] W) (h : i = j) :
    (s.changeEmbedding j h).principal = s.principal := by
  subst j
  rfl

@[simp] theorem ActualAnnealedInputs.changeEmbedding_weakRate
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (j : S →L[ℂ] W) (h : i = j) :
    (s.changeEmbedding j h).weakRate = s.weakRate := by
  subst j
  rfl

@[simp] theorem ActualAnnealedInputs.transportWeak_principal
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (e : W ≃ₗᵢ[ℂ] V) : (s.transportWeak e).principal = s.principal := rfl

@[simp] theorem ActualAnnealedInputs.transportWeak_weakRate
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {R : ℝ} (s : ActualAnnealedInputs law probability i R)
    (e : W ≃ₗᵢ[ℂ] V) : (s.transportWeak e).weakRate = s.weakRate := rfl

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
