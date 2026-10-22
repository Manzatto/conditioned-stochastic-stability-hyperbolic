module
public import ConditionedStochasticStabilityHyperbolic.Global.AugmentedFiltrationSource
public import ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource

/-! The paper's fixed absorbing base is constructed from a standard FULL
Conley filtration. Its first level is the absorbing attractor; the remaining
levels are in the computed graph order. Relative fixed-A filtration existence
is therefore not assumed as a classical theorem. -/
@[expose] public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedFiltration
open LeanShared ShiftedFiltrationGeometry PressureFiltrationSource
variable {X I : Type*} [MetricSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (L : List I)

def fullSets : Option I → Set X
  | none => isolatedCore T (closure A)
  | some i => Λ i

structure Produced (Dfull : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1)) where
  shift : ℕ
  shift_positive : 0 < shift
  source : AdaptedSource T A Λ L.length
  index : source.index = reversedVertex L
  positive_levels : ∀ j : ℕ, 0 < j →
    source.levels j = (T : X → X)^[shift] ⁻¹' Dfull.levels (j + 1)

/-- A standard full filtration and strict trapping produce the correctly
ordered, fixed-A filtration. All absorption and relabeling are derived. -/
def produce [CompactSpace X] (hA : IsOpen A) (hL : 0 < L.length)
    (strict : MapsTo T (closure A) A)
    (Dfull : AdaptedSource T ∅ (fullSets T A Λ) (L.length + 1))
    (first : Dfull.index ⟨0, by omega⟩ = none)
    (successor : ∀ i : Fin L.length,
      Dfull.index ⟨i.val + 1, by omega⟩ = some (reversedVertex L i))
    (retained : ∀ i : Fin L.length, Λ (reversedVertex L i) ⊆ Aᶜ) :
    Produced T A Λ L Dfull := Classical.choice (by
  have sets (i : Fin L.length) :
      AugmentedFiltrationSource.retainedSets T (fullSets T A Λ) L.length Dfull i =
        Λ (reversedVertex L i) := by
    simp only [AugmentedFiltrationSource.retainedSets, successor, fullSets]
  have attractor : isolatedCore T (Dfull.levels 1) = isolatedCore T (closure A) := by
    have core := Dfull.literal_core ⟨0, by omega⟩
    simpa only [filtrationLayer, Dfull.zero, Set.sdiff_empty, first, fullSets] using core
  have first_live : AugmentedFiltrationSource.retainedSets T (fullSets T A Λ)
      L.length Dfull ⟨0, hL⟩ ⊆ Aᶜ := by
    rw [sets]
    exact retained _
  obtain ⟨N, hN, E, index, levels⟩ := AugmentedFiltrationSource.exists_actualSource
    T (fullSets T A Λ) L.length Dfull A hA hL strict attractor first_live
  let source : AdaptedSource T A Λ L.length := {
    levels := E.levels
    index := reversedVertex L
    zero := E.zero
    monotone := E.monotone
    absorbing_forward := E.absorbing_forward
    compact_positive := E.compact_positive
    adapted_positive := E.adapted_positive
    terminal := E.terminal
    literal_core := by
      intro i
      have core := E.literal_core i
      rw [index] at core
      exact core.trans (sets i) }
  exact ⟨{
    shift := N
    shift_positive := hN
    source := source
    index := rfl
    positive_levels := levels }⟩)

end ConditionedStochasticStabilityHyperbolic.Global.OrderedAugmentedFiltration
