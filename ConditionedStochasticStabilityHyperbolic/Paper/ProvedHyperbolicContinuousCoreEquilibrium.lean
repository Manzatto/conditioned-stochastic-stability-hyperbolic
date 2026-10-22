module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicExpansivity
public import LeanShared.Dynamics.ContinuousCoreEquilibrium

/-! Literal fractional hyperbolic data construct an actual ambient equilibrium
for every potential continuous on the basic set, regardless of its values or
measurability outside that set. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle

theorem exists_equilibrium_continuousOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
    (h : BasicAnalyticData (E := E) T g Λ V)
    (φ : M → ℝ) (continuous : ContinuousOn φ Λ) :
    ∃ μ : ProbabilityMeasure M, LeanShared.ThermodynamicDefinitions.IsEquilibriumState T φ Λ μ := by
  obtain ⟨c,positive,expansive⟩ := h.exists_expansivity_radius
  exact LeanShared.ThermodynamicDefinitions.exists_equilibrium_of_continuousOn T Λ
    h.basic.hyperbolic.compact h.basic.nonempty h.basic.hyperbolic.invariant c positive expansive φ continuous

end ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
