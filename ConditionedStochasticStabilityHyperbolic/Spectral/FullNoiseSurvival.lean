module

public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstantSurvivalRankOne

/-! The actual fully live auxiliary noise chain has constant survival, for
any driving probability and any measurable noise map. Its leading raw rate
is exactly one, independent of its chosen normalization. -/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.FullNoiseSurvival

variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Ω]
  [OpensMeasurableSpace X]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
  (R : ℝ) (hR : 0 < R) (hOne : 1 ≤ R)

local notation "C" => NoiseKernel.chain ρ F hF univ MeasurableSet.univ
  (fun _ => 1) measurable_const R hR (fun _ => hOne)

theorem transfer_one (sf : HasStrongFellerKernel C) :
    strongFellerTransferOperator C sf 1 = R⁻¹ • (1 : X →ᵇ ℝ) := by
  ext x
  rw [strongFellerTransferOperator_represents,
    NoiseKernel.integral_chain ρ F hF univ MeasurableSet.univ
      (fun _ => 1) measurable_const (fun _ => zero_le_one) R hR (fun _ => hOne)
      (1 : X →ᵇ ℝ) (by fun_prop) x]
  simp

theorem raw_rate (sf : HasStrongFellerKernel C)
    (d : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : X →ᵇ ℝ)) :
    R * d.rate = 1 := by
  rw [d.rate_eq_of_constant_survival R⁻¹ (transfer_one ρ F hF R hR hOne sf)]
  exact mul_inv_cancel₀ hR.ne'

end ConditionedStochasticStabilityHyperbolic.FullNoiseSurvival
