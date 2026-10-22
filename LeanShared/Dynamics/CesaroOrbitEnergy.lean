module

public import LeanShared.Dynamics.CesaroProbability
public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Exact orbit-energy identity for the actual Cesaro probability. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.CesaroProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem orbit_energy (T : X → X) (continuous : Continuous T)
    (μ : ProbabilityMeasure X) (φ : X →ᵇ ℝ) (n : ℕ) :
    (∫ x, ThermodynamicDefinitions.orbitSum T φ (n+1) x ∂(μ : Measure X)) =
      (n+1 : ℝ)*(∫ x, φ x ∂measure T μ n) := by
  rw [integral T continuous.measurable μ n φ,←mul_assoc,
    mul_inv_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity),one_mul]
  exact integral_finsetSum (Finset.range (n+1))
    (fun j _ => (φ.compContinuous ⟨T^[j],continuous.iterate j⟩).integrable (μ : Measure X))

end LeanShared.CesaroProbability
