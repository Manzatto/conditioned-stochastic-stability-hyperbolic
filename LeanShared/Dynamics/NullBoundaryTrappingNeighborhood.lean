module
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.MetricSpace.Thickening

/-! Null-boundary trapping neighborhoods constructed by distance levels.
No differentiability of a boundary or a Sard theorem is needed. -/
public noncomputable section
open Set MeasureTheory Metric
namespace LeanShared.NullBoundaryTrappingNeighborhood
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A compact strict trapping set has an arbitrarily prescribed surrounding
compact trapping neighborhood with null boundary. The new set lies between
the original set and its one-step preimage, preserving the trapped core. -/
theorem exists_neighborhood (T : X → X) (continuous : Continuous T)
    (μ : Measure X) [SFinite μ] {K O : Set X} (compact : IsCompact K)
    (trapping : MapsTo T K (interior K)) (openO : IsOpen O) (inside : K ⊆ O) :
    ∃ D : Set X, IsCompact D ∧ K ⊆ interior D ∧ D ⊆ O ∧
      MapsTo T D (interior K) ∧ MapsTo T D (interior D) ∧ μ (frontier D) = 0 := by
  obtain ⟨δ, positive, safe⟩ := compact.exists_cthickening_subset_open
    (openO.inter (isOpen_interior.preimage continuous))
    (fun x hx => ⟨inside hx, trapping hx⟩)
  obtain ⟨r, range, boundary⟩ := exists_null_frontier_thickening μ K positive
  let D := closure (thickening r K)
  have contains : K ⊆ interior D :=
    (self_subset_thickening range.1 K).trans
      (isOpen_thickening.subset_interior_closure)
  have safeD : D ⊆ O ∩ T ⁻¹' interior K :=
    (closure_thickening_subset_cthickening r K).trans
      ((cthickening_mono range.2.le K).trans safe)
  have into : MapsTo T D (interior K) := fun x hx => (safeD hx).2
  refine ⟨D,isClosed_closure.isCompact,contains,fun x hx => (safeD hx).1,into,?_,?_⟩
  · exact fun x hx => (interior_mono (contains.trans interior_subset)) (into hx)
  · exact measure_mono_null frontier_closure_subset boundary
end LeanShared.NullBoundaryTrappingNeighborhood
