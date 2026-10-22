module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! The zero-noise raw transfer equals the actual deterministic generator;
no strong-Feller regularity is imposed at zero. -/
public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [MeasurableSpace Ω]

theorem ActualAnnealedInputs.raw_zero_of_constant_generators
    {law : ℝ≥0 → Measure Ω} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : E →L[ℂ] W} {R : ℝ}
    (inputs : ActualAnnealedInputs law prob i R) (hR : R ≠ 0)
    (P : E →L[ℂ] E) (hzero : ∀ z, inputs.generator 0 z = P) :
    (R : ℂ) • inputs.operator 0 = P := by
  let _ := prob 0
  apply ContinuousLinearMap.ext
  intro v
  change (R : ℂ) • (((R⁻¹ : ℝ) : ℂ) • ∫ z, inputs.generator 0 z v ∂law 0) = P v
  have integral_eq : (∫ z, inputs.generator 0 z v ∂law 0) = P v := by
    simp_rw [hzero]
    simp
  rw [integral_eq, smul_smul]
  have hs : (R : ℂ) * ((R⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hR]
    rfl
  rw [hs, one_smul]

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
