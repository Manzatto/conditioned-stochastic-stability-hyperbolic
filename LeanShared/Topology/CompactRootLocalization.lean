module
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-! Near the image of an injective map on a compact state space, all roots
of a jointly continuous parameter family stay near the original root. This
prevents remote inverse branches without assuming any inverse continuity. -/
public noncomputable section
namespace LeanShared.CompactRootLocalization
open Set Filter
open scoped Topology

theorem eventually_all_roots
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (F : A × X → Y) (continuous : Continuous F) (a : A) (x : X)
    (injective : Function.Injective (fun z => F (a,z)))
    (U : Set X) (openU : IsOpen U) (member : x ∈ U) :
    ∀ᶠ p : A × Y in 𝓝 (a,F (a,x)), ∀ z : X, F (p.1,z) = p.2 → z ∈ U := by
  let C : Set ((A × Y) × X) := {p | p.2 ∉ U ∧ F (p.1.1,p.2) = p.1.2}
  have closedC : IsClosed C :=
    (openU.isClosed_compl.preimage continuous_snd).inter
      (isClosed_eq (continuous.comp (continuous_fst.fst.prodMk continuous_snd)) continuous_fst.snd)
  have closedBad : IsClosed (Prod.fst '' C) := isClosedMap_fst_of_compactSpace C closedC
  have outside : (a,F (a,x)) ∉ Prod.fst '' C := by
    rintro ⟨⟨⟨b,y⟩,z⟩,⟨notin,equal⟩,pair⟩
    cases pair
    exact notin ((injective equal) ▸ member)
  have near := closedBad.isOpen_compl.mem_nhds outside
  filter_upwards [near] with p hp z equation
  by_contra notin
  exact hp ⟨(p,z),⟨notin,equation⟩,rfl⟩

end LeanShared.CompactRootLocalization
