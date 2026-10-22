module
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-! An actual compactly supported Euclidean smooth cutoff in any prescribed
open neighborhood of a compact set, without compactness of the ambient space. -/
public noncomputable section
open Set Metric
open scoped ContDiff
namespace LeanShared.CompactSmoothCutoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cutoff {K U : Set E} (compact : IsCompact K)
    (openU : IsOpen U) (inside : K⊆U) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ⊆U ∧
      (∀x,0≤ψ x ∧ ψ x≤1) ∧ EqOn ψ (fun _ => 1) K := by
  obtain ⟨δ,hδ,safe⟩ := compact.exists_cthickening_subset_open openU inside
  let O := thickening δ K
  have compactO : IsCompact (closure O) := compact.cthickening.of_isClosed_subset
    isClosed_closure (closure_thickening_subset_cthickening δ K)
  have safeO : closure O⊆U := (closure_thickening_subset_cthickening δ K).trans safe
  obtain ⟨ψ,hψ,rangeψ,supportψ,oneψ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=(⊤:ℕ∞)) (isOpen_thickening : IsOpen O) compact.isClosed (self_subset_thickening hδ K)
  refine ⟨ψ,hψ,?_,?_,fun x => rangeψ (mem_range_self x),fun x hx => (oneψ x).mp hx⟩
  · change IsCompact (closure (Function.support ψ))
    rw [supportψ]
    exact compactO
  · change closure (Function.support ψ)⊆U
    rw [supportψ]
    exact safeO
end LeanShared.CompactSmoothCutoff
