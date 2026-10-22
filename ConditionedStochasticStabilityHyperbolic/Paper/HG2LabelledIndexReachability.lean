module
public import ConditionedStochasticStabilityHyperbolic.Global.GreedySelectedIntervalEncoding
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.PaperHG2GreedySelection
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import LeanShared.Dynamics.TrappingBoundarySeparation

/-! Actual HG2 determines all greedy prefixes and their basin assignment.
Strict trapping is a separate, explicit hypothesis. Only existence of an
adapted filtration for this computed compatible order remains classical. -/
public noncomputable section
open Set Function Relation Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
open PaperHG2GreedySelection PressureFiltrationSource DerivedHG2Basins
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M}

omit [BorelSpace M] in
theorem adapted_interval_reachable (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ)
    (A : Set M) (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥)
    (D : AdaptedSource T A (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length)
    (index_eq : D.index = reversedVertex (greedy D0 g A h finitePressure).order)
    (s : Fin (greedy D0 g A h finitePressure).number)
    (i : Fin (((greedy D0 g A h finitePressure).terminal s).val + 1))
    (lower : ((greedy D0 g A h finitePressure).selectedRoot s).val ≤ i.val) :
    ReflTransGen (fun a b => D0.edge (D.index (originalIndex a)).val
      (D.index (originalIndex b)).val) i ((greedy D0 g A h finitePressure).selectedRoot s) := by
  have path := (greedy D0 g A h finitePressure).selected_interval_reachable s i lower
  simpa only [index_eq, PaperHG2GreedySelection.edge] using path

end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
