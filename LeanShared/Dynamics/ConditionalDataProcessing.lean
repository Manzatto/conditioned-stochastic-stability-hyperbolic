module

public import LeanShared.Dynamics.FiniteConditionalObservation

/-! Forgetting part of a finite conditioning observation cannot decrease
actual conditional Shannon entropy. -/
public noncomputable section
open Function MeasureTheory
namespace LeanShared.FiniteObservationEntropy
variable {X I J K : Type*} [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

theorem conditional_comp_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → I) (g : X → J) (p : J → K)
    (mf : Measurable f) (mg : Measurable g) (mp : Measurable p) :
    conditional μ f g ≤ conditional μ f (p ∘ g) := by
  have marginal := entropy_injective μ g (fun j => (p j,j))
    (fun _ _ equal => congrArg Prod.snd equal)
  have joint := entropy_injective μ (fun x => (f x,g x))
    (fun z : I × J => (z.1,(p z.2,z.2))) (by
      intro a b equal
      have first := congrArg Prod.fst equal
      have second := congrArg (fun z : I × (K × J) => z.2.2) equal
      exact Prod.ext first second)
  change entropy μ (fun x => (p (g x),g x))=entropy μ g at marginal
  change entropy μ (fun x => (f x,(p (g x),g x)))=entropy μ (fun x => (f x,g x)) at joint
  have bound := conditioning_decreases μ f (p ∘ g) g mf (mp.comp mg) mg
  dsimp only [conditional,Function.comp_def] at bound ⊢
  rw [joint,marginal] at bound
  exact bound

end LeanShared.FiniteObservationEntropy
