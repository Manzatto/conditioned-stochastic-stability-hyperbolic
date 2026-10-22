module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLDifferential
public import LeanShared.Dynamics.PressureRestriction

/-! Cutoff weights need equal exp(phi) only on the isolated basic set to
select the manuscript's geometric potential and equilibrium state. -/

@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared HyperbolicBasicSet ThermodynamicDefinitions
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

theorem potential_eq_exp_on_core (φ : M → ℝ)
    (hw : ∀ x ∈ Λ, g x = Real.exp (φ x)) :
    EqOn (h.basic.hyperbolic.potential g)
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ := by
  intro x hx
  simp only [HyperbolicData.potential, hw x hx, Real.log_exp]

theorem pressure_eq_exp_on_core (φ : M → ℝ)
    (hw : ∀ x ∈ Λ, g x = Real.exp (φ x)) :
    pressure T (h.basic.hyperbolic.potential g) Λ =
      pressure T (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ := by
  apply pressure_eq_of_eqOn
  · intro x hx
    rw [← h.basic.hyperbolic.invariant]
    exact mem_image_of_mem T hx
  · exact h.potential_eq_exp_on_core φ hw

variable [MeasurableSpace M] [BorelSpace M]
omit [BorelSpace M] in
theorem equilibrium_exp_on_core (φ : M → ℝ)
    (hw : ∀ x ∈ Λ, g x = Real.exp (φ x)) (ν : ProbabilityMeasure M) :
    IsEquilibriumState T (h.basic.hyperbolic.potential g) Λ ν ↔
      IsEquilibriumState T (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) Λ ν := by
  apply isEquilibriumState_iff_of_eqOn
  · intro x hx
    rw [← h.basic.hyperbolic.invariant]
    exact mem_image_of_mem T hx
  · exact h.potential_eq_exp_on_core φ hw

end ConditionedStochasticStabilityHyperbolic.Paper.HL
