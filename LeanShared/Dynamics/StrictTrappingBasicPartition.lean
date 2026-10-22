module

public import LeanShared.Dynamics.ReversibleTransitivity
public import LeanShared.Dynamics.TrappingBoundarySeparation

/-! # Strict trapping gives the basic-set partition required globally

An arbitrary forward-invariant open absorbing set may cut a transitive basic
set. Under the explicit strict condition T(closure A)⊆A, a transitive
forward-invariant set either lies entirely inside A or is separated from its
boundary. This supplies both the partition and the live interior condition;
it is not inferred from the manuscript's weaker literal HG1 premise.
-/

@[expose] public section
open Set
namespace LeanShared
open ControlledPlaqueClosure
variable {X : Type*} [MetricSpace X]

theorem transitive_subset_absorbing_of_intersection_strict_trapping
    (T : X ≃ₜ X) (A Λ : Set X) (hA : IsOpen A)
    (htrap : T '' closure A ⊆ A) (hforward : T '' Λ ⊆ Λ)
    (htrans : forwardTransitiveOn T Λ) (hmeet : (Λ ∩ A).Nonempty) : Λ ⊆ A := by
  have hTA : IsOpen (T '' A) := T.isOpenMap A hA
  have hTAforward : MapsTo T (T '' A) (T '' A) := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨T x, htrap ⟨x, subset_closure hx, rfl⟩, rfl⟩
  have hmeetTA : (Λ ∩ T '' A).Nonempty := by
    obtain ⟨x, hxΛ, hxA⟩ := hmeet
    exact ⟨T x, hforward ⟨x, hxΛ, rfl⟩, ⟨x, hxA, rfl⟩⟩
  have hclosed : IsClosed (T '' closure A) := T.isClosedMap _ isClosed_closure
  have horbits : (⋃ n : ℕ, (T : X → X)^[n] '' (Λ ∩ T '' A)) ⊆ T '' closure A := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.mp hy
    exact (image_mono subset_closure) (hTAforward.iterate n hx.2)
  exact (htrans (T '' A) hTA hmeetTA).trans ((closure_minimal horbits hclosed).trans htrap)

theorem transitive_basic_dichotomy_of_strict_trapping
    (T : X ≃ₜ X) (A Λ : Set X) (hA : IsOpen A)
    (htrap : T '' closure A ⊆ A) (hforward : T '' Λ ⊆ Λ)
    (htrans : forwardTransitiveOn T Λ) : Λ ⊆ A ∨ Λ ⊆ interior Aᶜ := by
  by_cases hmeet : (Λ ∩ A).Nonempty
  · exact Or.inl (transitive_subset_absorbing_of_intersection_strict_trapping
      T A Λ hA htrap hforward htrans hmeet)
  · apply Or.inr
    apply invariant_subset_interior_live_of_strict_trapping T A Λ htrap hforward
    exact disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hmeet)

end LeanShared
