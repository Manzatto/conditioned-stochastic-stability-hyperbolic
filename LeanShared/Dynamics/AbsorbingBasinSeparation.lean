module

public import LeanShared.Dynamics.StrictTrappingBasicPartition

/-! # Absorbed invariant sets cannot feed retained invariant sets

Forward invariance of A keeps backward basins of sets inside A inside A.
The positive distance to its boundary keeps forward basins of retained sets
outside A. Thus the absorbing attractor has no outgoing retained edge in
the full-filtration graph. The approach statements are the ordinary open
neighborhood formulation and make no spectral or probabilistic assumption.
-/

@[expose] public section
open Set Function
namespace LeanShared.AbsorbingBasinSeparation
variable {X : Type*} [TopologicalSpace X]

def Approaches (T : X → X) (Λ : Set X) (x : X) : Prop :=
  ∀ U : Set X, IsOpen U → Λ ⊆ U → ∃ n : ℕ, T^[n] x ∈ U

theorem backward_approach_mem_absorbing
    (T : X ≃ₜ X) (A Λ : Set X) (hA : IsOpen A)
    (hforward : MapsTo T A A) (hΛA : Λ ⊆ A) (x : X)
    (happroach : Approaches T.symm Λ x) : x ∈ A := by
  obtain ⟨n, hn⟩ := happroach A hA hΛA
  have h := hforward.iterate n hn
  have hc := T.right_inv.iterate n x
  change (T : X → X)^[n] ((T.symm : X → X)^[n] x) = x at hc
  rw [hc] at h
  exact h

theorem forward_approach_not_mem_absorbing
    (T : X ≃ₜ X) (A Λ : Set X) (hforward : MapsTo T A A)
    (hΛ : Λ ⊆ interior Aᶜ) (x : X)
    (happroach : Approaches T Λ x) : x ∉ A := by
  intro hx
  have hΛ' : Λ ⊆ (closure A)ᶜ := by
    simpa only [interior_compl] using hΛ
  obtain ⟨n, hn⟩ := happroach (closure A)ᶜ isClosed_closure.isOpen_compl hΛ'
  exact hn (subset_closure (hforward.iterate n hx))

theorem no_absorbed_to_retained_connection
    (T : X ≃ₜ X) (A Λabsorbed Λretained : Set X) (hA : IsOpen A)
    (hforward : MapsTo T A A) (habsorbed : Λabsorbed ⊆ A)
    (hretained : Λretained ⊆ interior Aᶜ) :
    ¬ ∃ x, Approaches T.symm Λabsorbed x ∧ Approaches T Λretained x := by
  rintro ⟨x, hpast, hfuture⟩
  exact forward_approach_not_mem_absorbing T A Λretained hforward hretained x hfuture
    (backward_approach_mem_absorbing T A Λabsorbed hA hforward habsorbed x hpast)

end LeanShared.AbsorbingBasinSeparation
