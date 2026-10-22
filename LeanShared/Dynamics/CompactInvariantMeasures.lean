module

public import LeanShared.Dynamics.CompactInvariantProbability
public import Mathlib.Topology.Semicontinuity.Basic

/-! Compactness of the actual invariant probability measures and
attainment of continuous orbit-average objectives. -/
public noncomputable section
open Set Function MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace LeanShared.EmpiricalProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Invariance is closed in the weak topology. -/
theorem isClosed_invariant (T : X → X) (continuous : Continuous T) :
    IsClosed {ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)} := by
  have identity : {ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)} =
      {ν | ν.map T=ν} := by
    ext ν
    constructor
    · intro invariant
      exact ProbabilityMeasure.toMeasure_injective invariant.map_eq
    · intro invariant
      exact ⟨continuous.measurable, congrArg ProbabilityMeasure.toMeasure invariant⟩
  rw [identity]
  exact isClosed_eq (ProbabilityMeasure.continuous_map continuous) continuous_id

/-- The invariant probability space is compact and nonempty. -/
theorem compact_nonempty_invariant [CompactSpace X] [Nonempty X]
    (T : X → X) (continuous : Continuous T) :
    IsCompact {ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)} ∧
      ({ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)}).Nonempty :=
  ⟨(isClosed_invariant T continuous).isCompact, exists_invariant_probability T continuous⟩

/-- A continuous potential has an actual maximizing invariant measure.
This is the zero-entropy optimization statement, without an assumed state. -/
theorem exists_maximizing_integral [CompactSpace X] [Nonempty X]
    (T : X → X) (continuous : Continuous T) (f : X →ᵇ ℝ) :
    ∃ ν : ProbabilityMeasure X, MeasurePreserving T (ν : Measure X) (ν : Measure X) ∧
      ∀ μ : ProbabilityMeasure X, MeasurePreserving T (μ : Measure X) (μ : Measure X) →
        (∫ x, f x ∂(μ : Measure X)) ≤ (∫ x, f x ∂(ν : Measure X)) := by
  obtain ⟨ν,invariant,maximal⟩ := (compact_nonempty_invariant T continuous).1.exists_isMaxOn
    (compact_nonempty_invariant T continuous).2
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).continuousOn
  exact ⟨ν,invariant,maximal⟩

end LeanShared.EmpiricalProbability
