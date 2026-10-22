module

public import LeanShared.Dynamics.IsolatingNeighborhood

/-! # Replacing a filtration's lower level by the actual absorbing set

If every point of an old lower level eventually enters A, no complete orbit
avoiding A can meet that lower level. If its original isolated core avoids
A, replacing the lower level preserves that core exactly. This deduction
supports a relative filtration built from the ordinary full filtration.
-/

@[expose] public section
open Set
namespace LeanShared
variable {X : Type*} [TopologicalSpace X]

theorem isolatedCore_avoids_eventually_absorbed
    (T : X ≃ₜ X) (K A B : Set X)
    (habs : ∀ y ∈ B, ∃ n : ℕ, (T : X → X)^[n] y ∈ A)
    {x : X} (hx : x ∈ isolatedCore T (K \ A)) : x ∉ B := by
  intro hxB
  obtain ⟨n, hn⟩ := habs x hxB
  exact (forwardTrapped_subset T (K \ A) (iterate_mem_isolatedCore T (K \ A) hx n).1).2 hn

theorem isolatedCore_subset_of_eventual_absorption
    (T : X ≃ₜ X) (K A B : Set X)
    (habs : ∀ y ∈ B, ∃ n : ℕ, (T : X → X)^[n] y ∈ A) :
    isolatedCore T (K \ A) ⊆ isolatedCore T (K \ B) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · intro n
    exact ⟨(hx.1 n).1, isolatedCore_avoids_eventually_absorbed T K A B habs
      (iterate_mem_isolatedCore T (K \ A) hx n)⟩
  · intro n
    exact ⟨(hx.2 n).1, isolatedCore_avoids_eventually_absorbed T K A B habs
      (iterate_symm_mem_isolatedCore T (K \ A) hx n)⟩

/-- No extra invariance of A or B is needed: eventual absorption and the
original complete-orbit core are the exact hypotheses. -/
theorem isolatedCore_replace_absorbing_base
    (T : X ≃ₜ X) (K A B : Set X)
    (habs : ∀ y ∈ B, ∃ n : ℕ, (T : X → X)^[n] y ∈ A)
    (hdis : Disjoint (isolatedCore T (K \ B)) A) :
    isolatedCore T (K \ A) = isolatedCore T (K \ B) := by
  apply Subset.antisymm (isolatedCore_subset_of_eventual_absorption T K A B habs)
  intro x hx
  refine ⟨?_, ?_⟩
  · intro n
    exact ⟨(hx.1 n).1, fun ha => Set.disjoint_left.mp hdis
      (iterate_mem_isolatedCore T (K \ B) hx n) ha⟩
  · intro n
    exact ⟨(hx.2 n).1, fun ha => Set.disjoint_left.mp hdis
      (iterate_symm_mem_isolatedCore T (K \ B) hx n) ha⟩

end LeanShared
