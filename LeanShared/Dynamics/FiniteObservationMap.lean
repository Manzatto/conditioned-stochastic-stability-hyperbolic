module

public import LeanShared.Dynamics.FiniteObservationEntropy
public import Mathlib.MeasureTheory.Measure.Map

/-! Exact finite observation entropy under actual measurable pushforward. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.FiniteObservationEntropy
variable {X Y I : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

theorem entropy_map (μ : Measure X) (f : X → Y) (measurable : Measurable f)
    (g : Y → I) (mg : Measurable g) :
    entropy (μ.map f) g=entropy μ (g ∘ f) := by
  simp only [entropy,Measure.real,Measure.map_apply measurable ((measurableSet_singleton _).preimage mg)]
  rfl

end LeanShared.FiniteObservationEntropy
