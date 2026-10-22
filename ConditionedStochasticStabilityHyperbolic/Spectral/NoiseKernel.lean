module

public import LeanShared.Probability.RandomMapKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedKernel

/-!
# Canonical weighted processes from measurable noise maps

Joint measurability of the random map and a probability noise law construct
the killed kernel and absorbing chain. The one-step representation is the
paper's weighted annealed integral, divided by a constant upper bound. The ambient state type is retained; application to the paper's process uses
starting states in the specified survival region.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace ConditionedStochasticStabilityHyperbolic.NoiseKernel

open LeanShared.RandomMapKernel

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Absorb at the cemetery when the random map exits the survival region or
when the normalized departure weight kills the trajectory. -/
def chain (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X)
    (hF : Measurable F) (U : Set X) (hU : MeasurableSet U)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) : AbsorbingMarkovChains.CanonicalChain X :=
  WeightedKernel.ofBoundedWeight (killed ρ F hF U hU) w R hw hR hwR
    (killed_mass_le_one ρ F hF U hU)

/-- The exact normalized weighted annealed operator for the constructed chain. -/
theorem integral_chain (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X)
    (hF : Measurable F) (U : Set X) (hU : MeasurableSet U)
    (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (f : X → ℝ) (hf : Measurable f) (x : X) :
    (∫ y, f y ∂(chain ρ F hF U hU w hw R hR hwR).killedTransition x) =
      (w x / R) * ∫ ω, U.indicator f (F (x, ω)) ∂ρ := by
  rw [chain, WeightedKernel.ofBoundedWeight_integral _ w R hw hw0 hR hwR,
    integral_killed ρ F hF U hU f hf x]

end ConditionedStochasticStabilityHyperbolic.NoiseKernel
