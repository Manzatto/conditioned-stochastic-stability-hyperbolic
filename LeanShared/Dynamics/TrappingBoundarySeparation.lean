module

public import Mathlib.Topology.MetricSpace.Thickening

/-! # Retained invariant sets are separated from a strict trapping boundary

The stronger trapping condition is explicit: the image of the closure of
the absorbing region lies in its interior. Mere forward invariance of an
open absorbing region does not provide this conclusion.
-/

@[expose] public section

namespace LeanShared

open Set Metric

theorem invariant_subset_compl_closure_of_strict_trapping
    {X : Type*} [TopologicalSpace X] (T : X → X) (A Λ : Set X)
    (htrap : T '' closure A ⊆ A) (hforward : T '' Λ ⊆ Λ)
    (hdis : Disjoint Λ A) : Λ ⊆ (closure A)ᶜ := by
  intro x hx hxA
  exact Set.disjoint_left.mp hdis (hforward ⟨x, hx, rfl⟩)
    (htrap ⟨x, hxA, rfl⟩)

theorem invariant_subset_interior_live_of_strict_trapping
    {X : Type*} [TopologicalSpace X] (T : X → X) (A Λ : Set X)
    (htrap : T '' closure A ⊆ A) (hforward : T '' Λ ⊆ Λ)
    (hdis : Disjoint Λ A) : Λ ⊆ interior (Aᶜ) := by
  rw [interior_compl]
  exact invariant_subset_compl_closure_of_strict_trapping T A Λ htrap hforward hdis

theorem exists_live_collar_of_strict_trapping
    {X : Type*} [PseudoMetricSpace X] (T : X → X) (A Λ : Set X)
    (hΛ : IsCompact Λ) (htrap : T '' closure A ⊆ A)
    (hforward : T '' Λ ⊆ Λ) (hdis : Disjoint Λ A) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ Λ ⊆ interior (Aᶜ) :=
  hΛ.exists_cthickening_subset_open isOpen_interior
    (invariant_subset_interior_live_of_strict_trapping T A Λ htrap hforward hdis)

/-- Strict trapping on a compact phase space survives a common uniform
perturbation threshold, including points on the absorbing boundary. -/
theorem exists_robust_strict_trapping
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (T : X → X) (hT : Continuous T) (A : Set X) (hA : IsOpen A)
    (htrap : T '' closure A ⊆ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
      (∀ x ∈ closure A, dist (F x) (T x) < δ) → F '' closure A ⊆ A := by
  obtain ⟨δ, hδ, hcollar⟩ := (isClosed_closure.isCompact.image hT).exists_thickening_subset_open
    hA htrap
  refine ⟨δ, hδ, ?_⟩
  intro F hF y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hcollar (mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, hF x hx⟩)

end LeanShared
