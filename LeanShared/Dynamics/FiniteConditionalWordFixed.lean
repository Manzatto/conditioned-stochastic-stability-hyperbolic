module

public import LeanShared.Dynamics.FiniteConditionalWord

/-! The entropy of an entire finite word, conditioned on one shared
observation, is bounded by the sum of its coordinate conditional entropies. -/
public noncomputable section
open Function MeasureTheory
open scoped BigOperators
namespace LeanShared.FiniteObservationEntropy
variable {X I J : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem conditional_word_fixed_le (μ : Measure X) [IsFiniteMeasure μ]
    (n : ℕ) (positive : 0 < n) (f : Fin n → X → I) (g : X → J)
    (mf : ∀ i, Measurable (f i)) (mg : Measurable g) :
    conditional μ (fun x i => f i x) g ≤ ∑ i : Fin n, conditional μ (f i) g := by
  let embed : J → (Fin n → J) := fun j _ => j
  have injective : Injective embed := by
    intro a b equal
    exact congrFun equal ⟨0,positive⟩
  have marginal := entropy_injective μ g embed injective
  have joint := entropy_injective μ (fun x => ((fun i : Fin n => f i x),g x))
    (Prod.map id embed) (by
      intro a b equal
      have first := congrArg Prod.fst equal
      have second := congrArg Prod.snd equal
      exact Prod.ext first (injective second))
  change entropy μ (fun x => ((fun i : Fin n => f i x),embed (g x))) =
    entropy μ (fun x => ((fun i : Fin n => f i x),g x)) at joint
  have bound := conditional_word_le μ n f (fun _ => g) mf (fun _ => mg)
  change entropy μ (fun x => ((fun i : Fin n => f i x),embed (g x))) -
    entropy μ (embed ∘ g) ≤ _ at bound
  rw [joint,marginal] at bound
  exact bound

end LeanShared.FiniteObservationEntropy
