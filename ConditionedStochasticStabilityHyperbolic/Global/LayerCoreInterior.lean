module

public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement

/-! Each basic set of an adapted filtration lies in the interior of its closed analytic layer.
Positive layers need nothing; the absorbing layer only needs that this particular basic set is
separated from the closure of the absorbing set. -/

public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.Global.LayerCoreInterior
open LeanShared ShiftedFiltrationGeometry FiltrationPressureConfinement FiltrationLayerGeometry
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ) (D : AdaptedSource T A Λ ℓ)

omit [MeasurableSpace X] [BorelSpace X] in
theorem core_subset_interior_closedLayer (i : Fin ℓ) (hsep : Λ (D.index i) ⊆ interior Aᶜ) :
    Λ (D.index i) ⊆ interior (closedLayer T A Λ ℓ N D i) := by
  refine Subset.trans ?_ (interior_mono subset_closure)
  change Λ (D.index i) ⊆ interior (filtrationLayer (levels T A Λ ℓ N D) i.val)
  by_cases hi : i.val = 0
  · rw [hi, filtrationLayer, zero_add, levels_zero]
    apply absorbing_core_subset_interior T (levels T A Λ ℓ N D 1) A (Λ (D.index i))
      (levels_positive_adapted T A Λ ℓ N D 1 (by omega) (by omega))
      _ hsep
    simpa only [hi, filtrationLayer, zero_add, levels_zero] using literal_core T A Λ ℓ N D i
  · rw [← literal_core T A Λ ℓ N D i, filtrationLayer]
    exact isolatedCore_subset_interior_stratum T _ _
      (levels_positive_compact T A Λ ℓ N D i.val (Nat.pos_of_ne_zero hi) (by omega)).isClosed
      (levels_positive_adapted T A Λ ℓ N D (i.val + 1) (by omega) (by omega))

end ConditionedStochasticStabilityHyperbolic.Global.LayerCoreInterior
