module

public import LeanShared.Dynamics.ExpansivePartitionLogEnvelope
public import LeanShared.Dynamics.ExpansivePressureLowerVariational

/-! The actual pressure of a compact expansive system controls every
separated partition sum up to a finite additive logarithmic envelope.
Pressure, entropy comparison and the envelope are all proved internally. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem actual_pressure_log_envelope (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
    (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧
      ∀ ε > 0, ∀ η > 0, ∃ A : ℝ, ∀ n : ℕ,
        Real.log (separatedPartitionSum T φ univ n ε).toReal ≤ (n : ℝ) * (P + η) + A := by
  obtain ⟨P, pressureP⟩ := finite_pressure_of_expansive T c positive expansive φ φ.continuous
  have maximal (ν : ProbabilityMeasure X)
      (invariant : MeasurePreserving T (ν : Measure X) (ν : Measure X)) :
      (entropy T (ν : Measure X)).toReal + ∫ x, φ x ∂(ν : Measure X) ≤ P := by
    have lower := entropy_free_energy_le_pressure T c positive expansive ν invariant φ
    obtain ⟨H, entropyH⟩ := entropy_finite_of_expansive T c positive expansive ν invariant
    rw [entropyH, ← EReal.coe_add, pressureP] at lower
    simpa only [entropyH, EReal.toReal_coe] using EReal.coe_le_coe_iff.mp lower
  exact ⟨P, pressureP, fun ε positiveε =>
    partition_log_envelope T c positive expansive φ P maximal ε positiveε⟩

end LeanShared.ThermodynamicDefinitions
