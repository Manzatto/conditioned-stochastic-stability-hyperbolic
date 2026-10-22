module
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-! A genuine smooth map near a compact Euclidean set has a global compactly
supported C1 representative agreeing on that exact set. -/
public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace LeanShared.CompactC1Extension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_compact_extension (g : E → F) {K U : Set E} (compact : IsCompact K)
    (openU : IsOpen U) (inside : K⊆U) (smooth : ContDiffOn ℝ 1 g U) :
    ∃ G : E → F, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ EqOn G g K := by
  obtain ⟨δ,hδ,safe⟩ := compact.exists_cthickening_subset_open openU inside
  let O := thickening δ K
  have compactO : IsCompact (closure O) := compact.cthickening.of_isClosed_subset
    isClosed_closure (closure_thickening_subset_cthickening δ K)
  have safeO : closure O⊆U := (closure_thickening_subset_cthickening δ K).trans safe
  obtain ⟨ψ,hψ,_,supportψ,oneψ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=(⊤:ℕ∞)) (isOpen_thickening : IsOpen O) compact.isClosed
    (self_subset_thickening hδ K)
  have compactψ : HasCompactSupport ψ := by
    change IsCompact (closure (Function.support ψ))
    rw [supportψ]
    exact compactO
  have safeψ : tsupport ψ⊆U := by
    change closure (Function.support ψ)⊆U
    rw [supportψ]
    exact safeO
  refine ⟨fun x => ψ x • g x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases active : x∈tsupport ψ
    · exact (hψ.of_le (by simp)).contDiffAt.smul ((smooth x (safeψ active)).contDiffAt (openU.mem_nhds (safeψ active)))
    · apply (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport ψ |>.isOpen_compl.mem_nhds active] with y hy
      have zero : ψ y=0 := image_eq_zero_of_notMem_tsupport hy
      simp only [zero,zero_smul]
  · exact compactψ.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left ψ g)
  · intro x hx
    change ψ x • g x = g x
    rw [(oneψ x).mp hx,one_smul]
end LeanShared.CompactC1Extension
