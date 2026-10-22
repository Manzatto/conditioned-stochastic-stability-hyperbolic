module
public import ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration

/-! Product-volume null boundaries are transported from the ordinary FULL
filtration; they are not assumed for the newly constructed absorbing base. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryFiltration
open LeanShared Global ShiftedFiltrationGeometry OrderedAugmentedFiltration
variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace (X × Y)]
  (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X) (Λ : I → Set X) (L : List I) (dominant : I)

theorem Data.product_positive_frontier_zero
    {full : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)}
    (d : Data T A Λ L dominant full) (σ : Measure (X × Y))
    (preimage_null : ∀ K : Set (X × Y), σ K = 0 → σ ((T.prodCongr S) ⁻¹' K) = 0)
    (full_null : ∀ j, 0 < j → j ≤ L.length + 1 →
      σ (frontier (full.levels j ×ˢ (univ : Set Y))) = 0)
    (j : ℕ) (hj : 0 < j) (bound : j ≤ L.length) :
    σ (frontier ((ProductAdaptedFiltration.source T S A Λ L.length
      (d.source T A Λ L dominant)).levels j)) = 0 := by
  rw [ProductAdaptedFiltration.source_levels]
  change σ (frontier (d.augmentation.source.levels j ×ˢ (univ : Set Y))) = 0
  rw [d.augmentation.positive_levels j hj]
  have same : (((T : X → X)^[d.augmentation.shift] ⁻¹' full.levels (j + 1)) ×ˢ
      (univ : Set Y)) =
      ((T.prodCongr S : X × Y → X × Y)^[d.augmentation.shift] ⁻¹'
        (full.levels (j + 1) ×ˢ univ)) := by
    ext z
    change ((T : X → X)^[d.augmentation.shift] z.1 ∈ full.levels (j + 1) ∧ z.2 ∈ univ) ↔
      (Prod.map (T : X → X) (S : Y → Y))^[d.augmentation.shift] z ∈
        (full.levels (j + 1) ×ˢ (univ : Set Y))
    rw [iterate_independent]
    simp only [mem_prod, mem_univ, and_true]
  rw [same, ← ShiftedBoundaryGeometry.preimage_iterate_frontier]
  exact ShiftedBoundaryGeometry.measure_preimage_iterate_zero (T.prodCongr S) σ preimage_null _
    (full_null (j + 1) (by omega) (by omega)) d.augmentation.shift

end ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryFiltration
