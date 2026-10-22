module

public import LeanShared.Analysis.CompactLocalHolder
public import Mathlib.Topology.MetricSpace.Thickening

/-! Local Hölder estimates on an open neighborhood give one quantitative
Hölder neighborhood of a compact set. Both the radius and constant are
constructed, including comparisons with points outside the compact set. -/
public noncomputable section
open Set Metric
namespace LeanShared.CompactLocalHolder
variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X] [MetricSpace Y]

theorem bound_near_compact {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (K U : Set X) (compact : IsCompact K) (openU : IsOpen U) (inside : K ⊆ U)
    (f : X → Y)
    (localBound : ∀ x ∈ U, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ W, ∀ z ∈ W,
        dist (f y) (f z) ≤ C * dist y z ^ a) :
    ∃ r > 0, ∃ C ≥ 0, ∀ x ∈ K, ∀ y : X, dist y x ≤ r →
      dist (f y) (f x) ≤ C * dist y x ^ a := by
  obtain ⟨r₀, positive₀, compact₀⟩ := compact.exists_isCompact_cthickening
  obtain ⟨r₁, positive₁, inside₁⟩ := compact.exists_cthickening_subset_open openU inside
  let r := min r₀ r₁
  have compactR : IsCompact (cthickening r K) := compact₀.of_isClosed_subset
    isClosed_cthickening (cthickening_mono (min_le_left _ _) K)
  have insideR : cthickening r K ⊆ U :=
    (cthickening_mono (min_le_right _ _) K).trans inside₁
  obtain ⟨C, nonnegative, bound⟩ := bound_on_compact ha ha1 compactR f
    (fun x hx => localBound x (insideR hx))
  refine ⟨r, lt_min positive₀ positive₁, C, nonnegative, fun x hx y hy => ?_⟩
  exact bound y (mem_cthickening_of_dist_le y x r K hx hy)
    x (self_subset_cthickening K hx)

end LeanShared.CompactLocalHolder
