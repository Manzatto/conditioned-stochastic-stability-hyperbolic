module
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.MetricSpace.Thickening

/-! A genuine smooth map near a compact Euclidean set has a global compactly
supported smooth representative agreeing on that exact set. -/
public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace LeanShared.CompactSmoothExtension
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_compact_extension (g : E → F) {K U : Set E} (compact : IsCompact K)
    (openU : IsOpen U) (inside : K⊆U) (smooth : ContDiffOn ℝ ∞ g U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ EqOn G g K := by
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
    · exact hψ.contDiffAt.smul ((smooth x (safeψ active)).contDiffAt (openU.mem_nhds (safeψ active)))
    · apply (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport ψ |>.isOpen_compl.mem_nhds active] with y hy
      have zero : ψ y=0 := image_eq_zero_of_notMem_tsupport hy
      simp only [zero,zero_smul]
  · exact compactψ.of_isClosed_subset (isClosed_tsupport _) (tsupport_smul_subset_left ψ g)
  · intro x hx
    change ψ x • g x = g x
    rw [(oneψ x).mp hx,one_smul]
/-- A C1 map on a neighborhood of a compact set has a global C1
representative agreeing on a neighborhood of EVERY point of that set. -/
theorem exists_extension {g : E → F} {K U : Set E} (compact : IsCompact K)
    (openU : IsOpen U) (inside : K⊆U) (smooth : ContDiffOn ℝ 1 g U) :
    ∃ G : E → F, ContDiff ℝ 1 G ∧ ∀x∈K, G =ᶠ[𝓝 x] g := by
  obtain ⟨δ,hδ,safe⟩ := compact.exists_cthickening_subset_open openU inside
  let O := thickening δ K
  let K₁ := cthickening (δ/2) K
  have compactO : IsCompact (closure O) := compact.cthickening.of_isClosed_subset
    isClosed_closure (closure_thickening_subset_cthickening δ K)
  have safeO : closure O⊆U := (closure_thickening_subset_cthickening δ K).trans safe
  have compactK₁ : IsCompact K₁ := compact.cthickening
  have inO : K₁⊆O := cthickening_subset_thickening' hδ (by linarith) K
  obtain ⟨ψ,hψ,_,supportψ,oneψ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=(⊤:ℕ∞)) (isOpen_thickening : IsOpen O) compactK₁.isClosed inO
  have safeψ : tsupport ψ⊆U := by
    change closure (Function.support ψ)⊆U
    rw [supportψ]
    exact safeO
  refine ⟨fun x => ψ x • g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases active : x∈tsupport ψ
    · exact (hψ.of_le (by simp)).contDiffAt.smul
        ((smooth x (safeψ active)).contDiffAt (openU.mem_nhds (safeψ active)))
    · apply (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport ψ |>.isOpen_compl.mem_nhds active] with y hy
      have zero : ψ y=0 := image_eq_zero_of_notMem_tsupport hy
      simp only [zero,zero_smul]
  · intro x hx
    have near : thickening (δ/2) K ∈ 𝓝 x :=
      isOpen_thickening.mem_nhds (self_subset_thickening (by linarith) K hx)
    filter_upwards [near] with y hy
    rw [(oneψ y).mp (thickening_subset_cthickening (δ/2) K hy),one_smul]
end LeanShared.CompactSmoothExtension
