module

public import LeanShared.Probability.WeightedRandomMapKernel

/-! Ordinary submersion absolute continuity of the UNWEIGHTED random-map
law already supplies absolute continuity of the inverse Jacobian-weighted
killed kernel. No separate weighted submersion theorem is needed. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionedStochasticStabilityHyperbolic.WeightedNoiseAbsoluteContinuity
open LeanShared
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

theorem weighted_transition_ac (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (W : X × Ω → ℝ) (hW : Measurable W)
    (x : X) : WeightedRandomMapKernel.transition ρ W F x ≪ RandomMapKernel.transition ρ F hF x := by
  rw [WeightedRandomMapKernel.transition_apply ρ W hW F hF x,
    RandomMapKernel.transition_apply]
  exact (withDensity_absolutelyContinuous ρ _).map (hF.comp measurable_prodMk_left)

theorem killed_ac_restricted_reference (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (W : X × Ω → ℝ) (hW : Measurable W)
    (σ : Measure X) (K : Set X) (hK : MeasurableSet K)
    (hac : ∀ x ∈ K, RandomMapKernel.transition ρ F hF x ≪ σ) :
    ∀ x ∈ K, WeightedRandomMapKernel.killed ρ W F K hK x ≪ σ.restrict K := by
  intro x hx
  exact ((weighted_transition_ac ρ F hF W hW x).trans (hac x hx)).restrict K

end ConditionedStochasticStabilityHyperbolic.WeightedNoiseAbsoluteContinuity
