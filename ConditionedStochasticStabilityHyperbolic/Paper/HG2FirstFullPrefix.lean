module
import all ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2GreedyFacts
public import ConditionedStochasticStabilityHyperbolic.Global.GreedyFirstPrefix
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies

/-! Numerical and actual-pressure facts for the computed HG2 prefixes. -/
public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
open PaperHG2GreedySelection PressureFiltrationSource DerivedHG2Basins AssembleShiftedPrefixFamilies
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M}
attribute [local instance] Classical.propDecidable

omit [BorelSpace M] in
theorem first_terminal_full (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥) :
    ((greedy D0 g A h finitePressure).terminal
      ⟨0, family_number_positive D0 g A h finitePressure⟩).val + 1 =
      (greedy D0 g A h finitePressure).order.length := by
  exact GreedyPrefixGeometry.first_terminal (edge D0 A) (pressure D0 g A)
    (acyclic D0 g A h) (pressure_injective D0 g A h finitePressure) _

end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
