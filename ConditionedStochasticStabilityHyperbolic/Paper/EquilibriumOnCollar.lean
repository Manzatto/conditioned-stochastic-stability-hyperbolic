module

public import ConditionedStochasticStabilityHyperbolic.Paper.ExponentialWeight
public import LeanShared.Probability.SupportedProbabilityLift

/-! The deterministic equilibrium state canonically determines the actual
probability on the closed live collar. A second unrelated limit probability
is not a source for the local stochastic-stability application. -/

@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)
  (e : EquilibriumPackage h.basic.hyperbolic g)
  (K : Set M) (hK : MeasurableSet K) (hΛK : Λ ⊆ K)

include hΛK in
omit [BorelSpace M] in
theorem equilibrium_carried : (e.state : Measure M) Kᶜ = 0 :=
  measure_mono_null (compl_subset_compl.mpr hΛK) e.equilibrium.2.2.1

def stateOnCollar : ProbabilityMeasure K :=
  SupportedProbabilityLift.probability K hK e.state (equilibrium_carried h e K hΛK)

omit [BorelSpace M] in
theorem stateOnCollar_map :
    ((h.stateOnCollar e K hK hΛK : ProbabilityMeasure K) : Measure K).map Subtype.val =
      (e.state : Measure M) :=
  SupportedProbabilityLift.map_probability K hK e.state (equilibrium_carried h e K hΛK)

omit [BorelSpace M] in
theorem stateOnCollar_unique (ν : ProbabilityMeasure K)
    (hν : (ν : Measure K).map Subtype.val = (e.state : Measure M)) :
    ν = h.stateOnCollar e K hK hΛK :=
  SupportedProbabilityLift.unique K hK e.state (equilibrium_carried h e K hΛK) ν hν

omit [BorelSpace M] in
theorem stateOnCollar_equilibrium (φ : M → ℝ)
    (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x)) :
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ e.state :=
  (h.equilibrium_exp_on_core φ hφ e.state).mp e.equilibrium

end ConditionedStochasticStabilityHyperbolic.Paper.HL
