module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Data.Finset.Basic

/-! A finite compact chart-patch cover supplies one close-pair selection
radius. Both points lie in the SAME chosen compact patch, with the first
point only required to belong to the covered compact set. -/
public noncomputable section
open Set Metric
namespace LeanShared.CompactPairChartSelection
variable {X I : Type*} [MetricSpace X]

theorem exists_radius (K : Set X) (compact : IsCompact K) (indices : Finset I)
    (patch : I → Set X) (cover : K ⊆ ⋃ i ∈ indices, interior (patch i)) :
    ∃ r > 0, ∀ x ∈ K, ∀ y : X, dist x y < r →
      ∃ i ∈ indices, x ∈ patch i ∧ y ∈ patch i := by
  classical
  let U := fun i : {i : I // i ∈ indices} => interior (patch i.val)
  have covers : K ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, hi, member⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, member⟩
  obtain ⟨r, positive, bound⟩ := lebesgue_number_lemma_of_metric (c := U) compact
    (fun i => isOpen_interior (s := patch i.val)) covers
  refine ⟨r, positive, fun x hx y close => ?_⟩
  obtain ⟨i, inside⟩ := bound x hx
  exact ⟨i.val, i.property, interior_subset (inside (mem_ball_self positive)),
    interior_subset (inside (by simpa only [mem_ball, dist_comm] using close))⟩

end LeanShared.CompactPairChartSelection
