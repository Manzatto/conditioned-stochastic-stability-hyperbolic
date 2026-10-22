module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Tactic.Linarith

/-! Local C¹ regularity at a compact set gives one genuine nonlinear radius.
The function need not be globally C¹ outside its chart domain. The same radius
can subsequently be rescaled by bounds on arbitrary (not continuously chosen)
linear frames. -/
public section
namespace LeanShared.CompactCenteredDerivativeBound
open Set Filter
open scoped Topology

theorem exists_radius_of_eventually
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    (K : Set P) (compact : IsCompact K) (property : P × E → Prop)
    (near : ∀ p ∈ K, ∀ᶠ z in 𝓝 (p, (0 : E)), property z) :
    ∃ R > 0, ∀ p ∈ K, ∀ v : E, ‖v‖ ≤ R → property (p, v) := by
  let O := interior {z | property z}
  have contains : K ×ˢ ({0} : Set E) ⊆ O := by
    rintro ⟨p, v⟩ ⟨hp, hv⟩
    rcases mem_singleton_iff.mp hv with rfl
    exact mem_interior_iff_mem_nhds.mpr (near p hp)
  obtain ⟨U, V, _, openV, cover, zeroV, tube⟩ :=
    generalized_tube_lemma compact isCompact_singleton isOpen_interior contains
  obtain ⟨r, positive, ball⟩ := Metric.mem_nhds_iff.mp
    (openV.mem_nhds (zeroV (mem_singleton 0)))
  refine ⟨r / 2, by linarith, fun p hp v small => ?_⟩
  apply interior_subset (tube ⟨cover hp, ball ?_⟩)
  rw [Metric.mem_ball, dist_zero_right]
  linarith

theorem exists_uniform_radius
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E) (compact : IsCompact K) (h : E → F)
    (smooth : ∀ a ∈ K, ContDiffAt ℝ 1 h a) (ε : ℝ) (positive : 0 < ε) :
    ∃ R > 0, ∀ a ∈ K, ∀ v : E, ‖v‖ ≤ R →
      ContDiffAt ℝ 1 h (a + v) ∧
      ‖fderiv ℝ h (a + v) - fderiv ℝ h a‖ < ε := by
  refine exists_radius_of_eventually K compact (fun z : E × E =>
    ContDiffAt ℝ 1 h (z.1 + z.2) ∧
      ‖fderiv ℝ h (z.1 + z.2) - fderiv ℝ h z.1‖ < ε) ?_
  intro a ha
  have addition : ContinuousAt (fun z : E × E => z.1 + z.2) (a, 0) :=
    continuousAt_fst.add continuousAt_snd
  have center : (fun z : E × E => z.1 + z.2) (a, 0) = a := add_zero a
  have near_smooth : ∀ᶠ z in 𝓝 (a, (0 : E)), ContDiffAt ℝ 1 h (z.1 + z.2) := by
    exact addition.tendsto.eventually (by simpa only [center] using
      ((smooth a ha).eventually (by norm_num)))
  have field := (smooth a ha).continuousAt_fderiv (by norm_num)
  have first : ContinuousAt (fun z : E × E => fderiv ℝ h (z.1 + z.2)) (a, 0) := by
    exact field.comp_of_eq addition center
  have second : ContinuousAt (fun z : E × E => fderiv ℝ h z.1) (a, 0) :=
    field.comp continuousAt_fst
  have remainder : ContinuousAt
      (fun z : E × E => ‖fderiv ℝ h (z.1 + z.2) - fderiv ℝ h z.1‖) (a, 0) :=
    (first.sub second).norm
  have limit : Tendsto
      (fun z : E × E => ‖fderiv ℝ h (z.1 + z.2) - fderiv ℝ h z.1‖)
      (𝓝 (a, (0 : E))) (𝓝 0) := by
    simpa only [ContinuousAt, add_zero, sub_self, norm_zero] using remainder
  have near_bound : ∀ᶠ z in 𝓝 (a, (0 : E)),
      ‖fderiv ℝ h (z.1 + z.2) - fderiv ℝ h z.1‖ < ε := by
    exact limit.eventually (gt_mem_nhds positive)
  exact near_smooth.and near_bound

end LeanShared.CompactCenteredDerivativeBound
