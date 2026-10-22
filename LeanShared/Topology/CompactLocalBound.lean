module
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-! A function locally bounded on a compact set has a single finite bound;
continuity of the function itself is not required. -/
public section
open Set Filter
open scoped Topology BigOperators
namespace LeanShared.CompactLocalBound
variable {X : Type*} [TopologicalSpace X]

theorem exists_bound {K : Set X} (compact : IsCompact K) (f : X → ℝ)
    (locallyBounded : ∀ x ∈ K, ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝[K] x, f y ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, f x ≤ C := by
  classical
  have possible (x : K) : ∃ C : ℝ, 0 < C ∧ ∃ U : Set X,
      IsOpen U ∧ x.val ∈ U ∧ ∀ y ∈ U, y ∈ K → f y ≤ C := by
    obtain ⟨C,hC,event⟩ := locallyBounded x x.property
    obtain ⟨U,nbd,bound⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp event
    obtain ⟨O,subset,openO,inside⟩ := mem_nhds_iff.mp nbd
    exact ⟨C,hC,O,openO,inside,fun y hy hk => bound ⟨subset hy,hk⟩⟩
  choose c positive U openU member bounded using possible
  obtain ⟨centers,covers⟩ := compact.elim_finite_subcover U openU
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,member ⟨x,hx⟩⟩)
  let C := 1+∑ x ∈ centers, c x
  have positiveC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun x _ => (positive x).le))
  refine ⟨C,positiveC,fun y hy => ?_⟩
  obtain ⟨x,hx,inside⟩ := mem_iUnion₂.mp (covers hy)
  exact (bounded x y inside hy).trans ((Finset.single_le_sum
    (fun j _ => (positive j).le) hx).trans (le_add_of_nonneg_left zero_le_one))
end LeanShared.CompactLocalBound
