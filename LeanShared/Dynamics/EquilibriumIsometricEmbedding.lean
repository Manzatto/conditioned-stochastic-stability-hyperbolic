module

public import LeanShared.Dynamics.PressureIsometricEmbedding
public import LeanShared.Dynamics.EntropyMeasurableEmbedding
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual isometric embeddings push actual equilibrium probabilities to
their exact image core, without ambient potential measurability assumptions. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]

theorem IsEquilibriumState.map_isometry (f : X → Y) (isometry : Isometry f)
    (embedding : MeasurableEmbedding f) (T : X → X) (S : Y → Y)
    (measurableS : Measurable S) (intertwine : Semiconj f T S)
    (φ : Y → ℝ) (μ : ProbabilityMeasure X)
    (state : IsEquilibriumState T (φ ∘ f) univ μ) :
    IsEquilibriumState S φ (range f) (μ.map f) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure (μ : Measure X)
  have invariant : ((μ : Measure X).map f).map S=(μ : Measure X).map f := by
    rw [Measure.map_map measurableS embedding.measurable,←intertwine.comp_eq,
      ←Measure.map_map embedding.measurable state.1,state.2.1]
  have entropyEq := entropy_map_embedding f embedding T S intertwine measurableS (μ : Measure X)
  have integrable : Integrable φ ((μ : Measure X).map f) := embedding.integrable_map_iff.mpr state.2.2.2.1
  refine ⟨measurableS,invariant,?_,integrable,?_⟩
  · change (μ : Measure X).map f (range f)ᶜ=0
    rw [Measure.map_apply embedding.measurable embedding.measurableSet_range.compl]
    simp
  · change entropy S ((μ : Measure X).map f)+((∫ y, φ y ∂((μ : Measure X).map f) : ℝ) : EReal)=_
    rw [entropyEq,embedding.integral_map φ,←pressure_embedding f isometry T S intertwine φ]
    exact state.2.2.2.2

end LeanShared.ThermodynamicDefinitions
