module

public import LeanShared.Dynamics.FiniteObservationEntropy

/-! Exact entropy identities for actual finite tuple observations. -/
public noncomputable section
namespace LeanShared.FiniteObservationEntropy
open Function MeasureTheory
variable {X I J K : Type*} [MeasurableSpace X] [Fintype I] [Fintype J] [Fintype K]

theorem pair_swap (μ : Measure X) (f : X → I) (g : X → J) :
    entropy μ (fun x => (f x,g x))=entropy μ (fun x => (g x,f x)) :=
  (entropy_injective μ (fun x => (f x,g x)) (Equiv.prodComm I J)
    (Equiv.prodComm I J).injective).symm

theorem pair_assoc (μ : Measure X) (f : X → I) (g : X → J) (h : X → K) :
    entropy μ (fun x => ((f x,g x),h x))=entropy μ (fun x => (f x,(g x,h x))) :=
  (entropy_injective μ (fun x => ((f x,g x),h x)) (Equiv.prodAssoc I J K)
    (Equiv.prodAssoc I J K).injective).symm

theorem triple_swap_first (μ : Measure X) (f : X → I) (g : X → J) (h : X → K) :
    entropy μ (fun x => (f x,(g x,h x)))=entropy μ (fun x => (g x,(f x,h x))) := by
  rw [←pair_assoc,←pair_assoc]
  exact entropy_injective μ (fun x => ((g x,f x),h x))
    (fun p => ((p.1.2,p.1.1),p.2))
    (fun a b equal => by
      rcases a with ⟨⟨a₁,a₂⟩,a₃⟩
      rcases b with ⟨⟨b₁,b₂⟩,b₃⟩
      simp only [Prod.mk.injEq] at equal ⊢
      exact ⟨⟨equal.1.2,equal.1.1⟩,equal.2⟩)

end LeanShared.FiniteObservationEntropy
