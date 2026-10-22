module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicExpansivity
public import LeanShared.Dynamics.ExpansiveInvariantPressure

/-! Actual finite pressure derived from the literal fractional-regular
hyperbolic dynamics, without an expansive or pressure-finiteness source. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

theorem finite_pressure
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
    (h : BasicAnalyticData (E := E) T g Λ V)
    (φ : M → ℝ) (continuous : ContinuousOn φ Λ) :
    ∃ P : ℝ, LeanShared.ThermodynamicDefinitions.pressure T φ Λ=(P : EReal) := by
  obtain ⟨c,positive,expansive⟩ := h.exists_expansivity_radius
  exact LeanShared.ThermodynamicDefinitions.finite_pressure_on_compact_expansive T Λ
    h.basic.hyperbolic.compact h.basic.nonempty h.basic.hyperbolic.invariant c positive expansive φ continuous

end ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
