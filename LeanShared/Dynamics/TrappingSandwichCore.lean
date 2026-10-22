module
public import LeanShared.Dynamics.ShiftedFiltration

/-! Replacing a trapping level between itself and one preimage preserves
the full trapped cores on both sides of its boundary. -/
public section
open Set
namespace LeanShared.TrappingSandwichCore
variable {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X)

theorem mono {K L : Set X} (inside : K ⊆ L) : isolatedCore T K ⊆ isolatedCore T L :=
  fun _ h => ⟨fun n => inside (h.1 n),fun n => inside (h.2 n)⟩

theorem core {K D : Set X} (inside : K ⊆ D) (outside : D ⊆ T ⁻¹' K) :
    isolatedCore T D = isolatedCore T K := by
  apply Subset.antisymm
  · have h := mono T outside
    simpa only [show T ⁻¹' K = (T : X → X)^[1] ⁻¹' K from rfl,
      isolatedCore_preimage_iterate] using h
  · exact mono T inside

theorem complement {K D : Set X} (inside : K ⊆ D) (outside : D ⊆ T ⁻¹' K) :
    isolatedCore T Dᶜ = isolatedCore T Kᶜ := by
  apply Subset.antisymm (mono T (compl_subset_compl.mpr inside))
  have h : isolatedCore T ((T ⁻¹' K)ᶜ) ⊆ isolatedCore T Dᶜ :=
    mono T (compl_subset_compl.mpr outside)
  simpa only [← preimage_compl,
    show T ⁻¹' Kᶜ = (T : X → X)^[1] ⁻¹' Kᶜ from rfl,
    isolatedCore_preimage_iterate] using h

theorem layer {K L D F : Set X} (insideK : K ⊆ D) (outsideK : D ⊆ T ⁻¹' K)
    (insideL : L ⊆ F) (outsideL : F ⊆ T ⁻¹' L) :
    isolatedCore T (D \ F) = isolatedCore T (K \ L) := by
  rw [isolatedCore_sdiff,isolatedCore_sdiff,
    core T insideK outsideK,complement T insideL outsideL]
end LeanShared.TrappingSandwichCore
