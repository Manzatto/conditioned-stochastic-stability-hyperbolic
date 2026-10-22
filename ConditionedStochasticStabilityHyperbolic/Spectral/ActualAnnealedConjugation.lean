module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
public import ConditionedStochasticStabilityHyperbolic.Spectral.CoreConjugation

/-! Continuous conjugation derived from the actual smooth core commutes with
varying-law averages and real normalization. No analytic averaged-operator
conjugation is assumed. -/

public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.AnnealedOperatorBounds

variable {S W Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [MeasurableSpace Ω]

def ActualAnnealedInputs.conjugation_of_generators
    {law : ℝ≥0 → Measure Ω} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {scale : ℝ}
    (s : ActualAnnealedInputs law probability i scale)
    (J : S →L[ℝ] S) (hinvolutive : Function.Involutive J)
    (hstar : ∀ (z : ℂ) x, J (z • x) = star z • J x)
    (hcomm : ∀ ε z x, s.generator ε z (J x) = J (s.generator ε z x)) (ε : ℝ≥0) :
    RealOperatorConjugation (s.operator ε) where
  conjugate := J
  involutive := hinvolutive
  zero := map_zero _
  smul := hstar
  commute := by
    let _ := probability ε
    intro x
    change (((scale⁻¹ : ℝ) : ℂ) • ∫ z, s.generator ε z (J x) ∂law ε) =
      J (((scale⁻¹ : ℝ) : ℂ) • ∫ z, s.generator ε z x ∂law ε)
    rw [hstar]
    simp only [Complex.star_def, Complex.conj_ofReal]
    congr 1
    rw [← J.integral_comp_comm (random_apply_integrable (law ε) (s.generator ε)
      (s.measurable ε) s.operatorBound (s.generator_bound ε) x)]
    exact integral_congr_ae (ae_of_all _ fun z => hcomm ε z x)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
