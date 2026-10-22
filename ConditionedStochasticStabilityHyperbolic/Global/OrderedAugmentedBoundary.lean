module
public import ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedFiltration

/-! Null boundaries for the constructed fixed-base filtration are consequences
of the ordinary full filtration's positive smooth boundaries. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedFiltration
open LeanShared ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (L : List I)

theorem Produced.positive_frontier_zero
    {Dfull : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)}
    (p : Produced T A Λ L Dfull) (σ : Measure X)
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (hnull : ∀ j, 0 < j → j ≤ L.length + 1 →
      σ (frontier (Dfull.levels j)) = 0)
    (j : ℕ) (hj : 0 < j) (hbound : j ≤ L.length) :
    σ (frontier (p.source.levels j)) = 0 := by
  rw [p.positive_levels j hj, ← ShiftedBoundaryGeometry.preimage_iterate_frontier]
  exact ShiftedBoundaryGeometry.measure_preimage_iterate_zero T σ hpre _
    (hnull (j + 1) (by omega) (by omega)) p.shift

theorem Produced.positive_frontier_zero_of_smooth
    {Dfull : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)}
    (p : Produced T A Λ L Dfull) (σ : Measure X)
    (hpre : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (SmoothLevel : Set X → Prop)
    (smooth : ∀ j, 0 < j → j ≤ L.length + 1 → SmoothLevel (Dfull.levels j))
    (null : ∀ K, SmoothLevel K → σ (frontier K) = 0) :
    ∀ j, 0 < j → j ≤ L.length → σ (frontier (p.source.levels j)) = 0 := by
  exact p.positive_frontier_zero T A Λ L σ hpre
    (fun j hj hbound => null _ (smooth j hj hbound))

end ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedFiltration
