module

public import LeanShared.Dynamics.CesaroOrbitEnergy
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Actual invariant potential energy scales exactly with the orbit horizon. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem integrable_orbitSum (T : X → X) (continuous : Continuous T)
    (μ : Measure X) [IsFiniteMeasure μ] (φ : X →ᵇ ℝ) (n : ℕ) :
    Integrable (orbitSum T φ n) μ := by
  exact integrable_finsetSum _ (fun j _ => (φ.compContinuous ⟨T^[j],continuous.iterate j⟩).integrable μ)

theorem integral_orbitSum_invariant (T : X → X) (μ : Measure X) [IsFiniteMeasure μ]
    (invariant : MeasurePreserving T μ μ) (φ : X →ᵇ ℝ) (n : ℕ) :
    (∫ x, orbitSum T φ n x ∂μ) = (n : ℝ)*(∫ x, φ x ∂μ) := by
  have integrable (j : ℕ) : Integrable (fun x => φ (T^[j] x)) μ :=
    Integrable.comp_measurable (by rw [(invariant.iterate j).map_eq]; exact φ.integrable μ)
      (invariant.iterate j).measurable
  have equal (j : ℕ) : (∫ x, φ (T^[j] x) ∂μ) = ∫ x, φ x ∂μ := by
    have h := integral_map_of_stronglyMeasurable (μ := μ) (invariant.iterate j).measurable φ.continuous.stronglyMeasurable
    rw [(invariant.iterate j).map_eq] at h
    exact h.symm
  change (∫ x, ∑ j ∈ Finset.range n, φ (T^[j] x) ∂μ) = _
  rw [integral_finsetSum _ (fun j _ => integrable j)]
  simp only [equal,Finset.sum_const,Finset.card_range,nsmul_eq_mul]

end LeanShared.ThermodynamicDefinitions
