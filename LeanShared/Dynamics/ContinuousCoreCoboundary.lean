module

public import LeanShared.Dynamics.EquilibriumCoboundary
public import LeanShared.Dynamics.CoreContinuousIntegrability

/-! Continuous core coboundaries preserve actual pressure and exactly
all actual equilibrium probabilities, with no ambient transfer regularity. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem pressure_continuous_core_coboundary (T : X → X) (K : Set X)
    (compact : IsCompact K) (invariant : MapsTo T K K) (φ ψ u : X → ℝ)
    (continuous : ContinuousOn u K) (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x)) :
    pressure T φ K=pressure T ψ K := by
  obtain ⟨B,bound⟩ := (compact.image_of_continuousOn continuous.abs).bddAbove
  exact pressure_coboundary invariant B (fun x hx => bound (mem_image_of_mem _ hx)) same

theorem isEquilibriumState_iff_continuous_core_coboundary (T : X → X) (K : Set X)
    (compact : IsCompact K) (invariant : MapsTo T K K) (φ ψ u : X → ℝ)
    (continuous : ContinuousOn u K) (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x))
    (μ : ProbabilityMeasure X) : IsEquilibriumState T φ K μ ↔ IsEquilibriumState T ψ K μ := by
  constructor
  · intro state
    obtain ⟨B,_,bound,integrable⟩ := bounded_integrable_of_continuousOn_compact K compact u continuous
      (μ : Measure X) state.2.2.1
    exact (isEquilibriumState_iff_coboundary T K invariant φ ψ u B bound same μ integrable).mp state
  · intro state
    obtain ⟨B,_,bound,integrable⟩ := bounded_integrable_of_continuousOn_compact K compact u continuous
      (μ : Measure X) state.2.2.1
    exact (isEquilibriumState_iff_coboundary T K invariant φ ψ u B bound same μ integrable).mpr state

end LeanShared.ThermodynamicDefinitions
