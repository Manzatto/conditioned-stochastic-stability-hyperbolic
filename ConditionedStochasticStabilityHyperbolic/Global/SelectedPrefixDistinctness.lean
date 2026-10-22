module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedPrefixQuasiErgodic

/-! # Distinctness of the actual selected-prefix probabilities

A selected root in a higher literal layer lies outside every lower prefix.
The lower prefix product is supported in that closed prefix; the higher
selected product gives support to its root. Their probabilities are therefore
different, without an assumed separation of physical probability measures.
-/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixDistinctness
open LeanShared ShiftedFiltrationGeometry FiltrationLayerGeometry
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem mapped_prefix_measure_support_subset (P : Set X) (hP : IsClosed P) (μ : Measure P) :
    (μ.map Subtype.val).support ⊆ P := by
  apply Measure.support_subset_of_isClosed hP
  rw [mem_ae_iff]
  rw [Measure.map_apply measurable_subtype_coe hP.measurableSet.compl]
  have he : (Subtype.val : P → X) ⁻¹' Pᶜ = ∅ := by
    ext x
    exact ⟨fun h => False.elim (h x.property), fun h => False.elim h⟩
  rw [he, measure_empty]

omit [MeasurableSpace X] [BorelSpace X] in
theorem selected_root_outside_lower_prefix
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (j : Fin ℓ) (hkj : k ≤ j.val) :
    Λ (D.index j) ⊆ (levels T A Λ ℓ N D k)ᶜ := by
  intro x hx hlow
  have hcore : x ∈ isolatedCore T (filtrationLayer (levels T A Λ ℓ N D) j.val) :=
    (literal_core T A Λ ℓ N D j).symm ▸ hx
  have hstratum := forwardTrapped_subset T _ hcore.1
  exact hstratum.2 (levels_monotone T A Λ ℓ N D hkj hlow)

/-- This is the actual measure-distinctness conclusion for two selected
blocks; both root support and the lower product come from their producers. -/
theorem actual_selected_products_ne
    (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hk : 0 < k) (hkℓ : k ≤ ℓ)
    (j : Fin ℓ) (hkj : k ≤ j.val) (hroot : (Λ (D.index j)).Nonempty)
    (μ : Measure (levels T A Λ ℓ N D k)) (ν : Measure X)
    (hν : Λ (D.index j) ⊆ ν.support) : μ.map Subtype.val ≠ ν := by
  intro heq
  obtain ⟨x, hx⟩ := hroot
  have hxν := hν hx
  rw [← heq] at hxν
  have hxprefix := mapped_prefix_measure_support_subset _
    (levels_positive_compact T A Λ ℓ N D k hk hkℓ).isClosed μ hxν
  exact selected_root_outside_lower_prefix T A Λ ℓ N D k j hkj hx hxprefix

end ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixDistinctness
