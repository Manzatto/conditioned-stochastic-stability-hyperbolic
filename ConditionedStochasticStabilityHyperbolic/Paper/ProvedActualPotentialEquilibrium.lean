module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicContinuousCoreEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicFinitePressure
public import LeanShared.Dynamics.HyperbolicPotentialContinuity

/-! Literal fractional hyperbolic analytic data construct finite pressure
and an actual equilibrium for log(g) minus the actual unstable log-Jacobian.
No pressure, potential-continuity or equilibrium-existence source is supplied.
Uniqueness requires additional thermodynamic work and is not asserted here. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem actual_potential_continuousOn (h : BasicAnalyticData (E := E) T g Λ V) :
    ContinuousOn (h.basic.hyperbolic.potential g) Λ := by
  have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  have forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T :=
    h.map_regular.differentiable.of_le (by exact_mod_cast hn)
  have inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm :=
    h.inverse_regular.differentiable.of_le (by exact_mod_cast hn)
  exact h.basic.hyperbolic.continuousOn_potential forward
    (inverse.mdifferentiable (by norm_num)) g
    h.weight_regular.differentiable.continuous.continuousOn h.weight_positive

theorem actual_thermodynamic_existence (h : BasicAnalyticData (E := E) T g Λ V) :
    ∃ P : ℝ, ∃ μ : ProbabilityMeasure M,
      LeanShared.ThermodynamicDefinitions.pressure T (h.basic.hyperbolic.potential g) Λ=(P : EReal) ∧
      LeanShared.ThermodynamicDefinitions.IsEquilibriumState T (h.basic.hyperbolic.potential g) Λ μ := by
  obtain ⟨P,pressure⟩ := h.finite_pressure _ h.actual_potential_continuousOn
  obtain ⟨μ,equilibrium⟩ := h.exists_equilibrium_continuousOn _ h.actual_potential_continuousOn
  exact ⟨P,μ,pressure,equilibrium⟩

end ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
