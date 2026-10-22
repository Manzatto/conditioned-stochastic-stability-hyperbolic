module
public import ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedBoundary
public import ConditionedStochasticStabilityHyperbolic.Global.PressurePrefixSelection

/-! Ordinary full-filtration data construct the actual fixed absorbing base
and its selected dominant layer. No relative filtration is a cited input. -/
@[expose] public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryFiltration
open LeanShared Global ShiftedFiltrationGeometry OrderedAugmentedFiltration
variable {X I : Type*} [MetricSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (L : List I) (dominant : I)

structure Data (full : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)) where
  augmentation : Produced T A Λ L full
  selected : Fin L.length
  selected_dominant : augmentation.source.index selected = dominant

def Data.source {full : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)}
    (d : Data T A Λ L dominant full) : AdaptedSource T A Λ L.length :=
  d.augmentation.source

def produce [CompactSpace X] (hA : IsOpen A) (strict : MapsTo T (closure A) A)
    (full : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1))
    (first : full.index ⟨0, by omega⟩ = none)
    (successor : ∀ i : Fin L.length,
      full.index ⟨i.val + 1, by omega⟩ = some (PressureFiltrationSource.reversedVertex L i))
    (retained : ∀ i : Fin L.length, Λ (PressureFiltrationSource.reversedVertex L i) ⊆ Aᶜ)
    (member : dominant ∈ L) : Data T A Λ L dominant full := Classical.choice (by
  obtain ⟨i, hi⟩ : ∃ i : Fin L.length, PressureFiltrationSource.reversedVertex L i = dominant := by
    simpa only [List.nil_append] using
      PressurePrefixSelection.exists_reversed_prefix_index ([] : List I) L dominant member
  let p := OrderedAugmentedFiltration.produce T A Λ L hA (by have := i.isLt; omega)
    strict full first successor retained
  exact ⟨{ augmentation := p, selected := i, selected_dominant := by rw [p.index]; exact hi }⟩)

theorem Data.positive_frontier_zero [MeasurableSpace X]
    {full : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)}
    (d : Data T A Λ L dominant full) (σ : Measure X)
    (preimage_null : ∀ K : Set X, σ K = 0 → σ (T ⁻¹' K) = 0)
    (full_null : ∀ j, 0 < j → j ≤ L.length + 1 → σ (frontier (full.levels j)) = 0) :
    ∀ j, 0 < j → j ≤ L.length → σ (frontier ((d.source T A Λ L dominant).levels j)) = 0 :=
  d.augmentation.positive_frontier_zero T A Λ L σ preimage_null full_null

end ConditionedStochasticStabilityHyperbolic.Paper.HG1OrdinaryFiltration
