module

public import LeanShared.Dynamics.PressureCoboundary
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual bounded coboundaries preserve exactly the ambient equilibrium
probabilities whenever their transfer function is integrable for that law. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

private theorem equilibrium_of_integrable_coboundary
    (T : X → X) (K : Set X) (φ ψ u : X → ℝ) (μ : ProbabilityMeasure X)
    (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x))
    (pressureEq : pressure T φ K=pressure T ψ K) (integrableU : Integrable u (μ : Measure X))
    (state : IsEquilibriumState T φ K μ) : IsEquilibriumState T ψ K μ := by
  have mappedU : Integrable u ((μ : Measure X).map T) := by rw [state.2.1]; exact integrableU
  have composedU := mappedU.comp_measurable state.1
  have integralU := integral_map state.1.aemeasurable mappedU.aestronglyMeasurable
  rw [state.2.1] at integralU
  have equal : ψ =ᵐ[(μ : Measure X)] (fun x => φ x-u x+u (T x)) := by
    filter_upwards [mem_ae_iff.mpr state.2.2.1] with x hx
    linarith [same x hx]
  have hint := (state.2.2.2.1.sub integrableU).add composedU
  have integralEq : (∫ x, ψ x ∂(μ : Measure X))=∫ x, φ x ∂(μ : Measure X) := by
    rw [integral_congr_ae equal]
    have sumInt : (∫ x, φ x-u x+u (T x) ∂(μ : Measure X)) =
        (∫ x, φ x-u x ∂(μ : Measure X))+(∫ x, u (T x) ∂(μ : Measure X)) :=
      integral_add (state.2.2.2.1.sub integrableU) composedU
    have subInt : (∫ x, φ x-u x ∂(μ : Measure X)) =
        (∫ x, φ x ∂(μ : Measure X))-(∫ x, u x ∂(μ : Measure X)) := integral_sub state.2.2.2.1 integrableU
    linarith
  refine ⟨state.1,state.2.1,state.2.2.1,hint.congr equal.symm,?_⟩
  rw [integralEq,←pressureEq]
  exact state.2.2.2.2

theorem isEquilibriumState_iff_coboundary (T : X → X) (K : Set X)
    (invariant : MapsTo T K K) (φ ψ u : X → ℝ) (B : ℝ)
    (bounded : ∀ x ∈ K, |u x| ≤ B)
    (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x))
    (μ : ProbabilityMeasure X) (integrableU : Integrable u (μ : Measure X)) :
    IsEquilibriumState T φ K μ ↔ IsEquilibriumState T ψ K μ := by
  have pressureEq := pressure_coboundary invariant B bounded same
  refine ⟨equilibrium_of_integrable_coboundary T K φ ψ u μ same pressureEq integrableU,?_⟩
  apply equilibrium_of_integrable_coboundary T K ψ φ (fun x => -u x) μ ?_ pressureEq.symm integrableU.neg
  intro x hx
  linarith [same x hx]

end LeanShared.ThermodynamicDefinitions
