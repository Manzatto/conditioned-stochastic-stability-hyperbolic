module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Hausdorff

/-! A compact set admits finitely many compact ambient neighborhoods inside
any prescribed pointwise open neighborhoods. Interiors still cover the set. -/
public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.FiniteCompactNeighborhoodCover
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem exists_cover (K : Set X) (compact : IsCompact K)
    (U : X → Set X) (openU : ∀ x, IsOpen (U x)) (inside : ∀ x ∈ K, x ∈ U x) :
    ∃ centers : Finset K, ∃ patch : K → Set X,
      (∀ x, IsCompact (patch x) ∧ patch x ⊆ U x ∧ x.val ∈ interior (patch x)) ∧
      K ⊆ ⋃ x ∈ centers, interior (patch x) := by
  classical
  have possible (x : K) : ∃ C : Set X, C ∈ 𝓝 x.val ∧ IsClosed C ∧ C ⊆ U x :=
    exists_mem_nhds_isClosed_subset ((openU x).mem_nhds (inside x x.property))
  choose C neighborhood closed subset using possible
  have member (x : K) : x.val ∈ interior (C x) := mem_interior_iff_mem_nhds.mpr (neighborhood x)
  obtain ⟨centers,covers⟩ := compact.elim_finite_subcover
    (fun x : K => interior (C x)) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,member ⟨x,hx⟩⟩)
  exact ⟨centers,C,fun x => ⟨(closed x).isCompact,subset x,member x⟩,covers⟩
end LeanShared.FiniteCompactNeighborhoodCover
