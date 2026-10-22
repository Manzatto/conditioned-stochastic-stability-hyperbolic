module
public import LeanShared.Analysis.CompactSmoothExtension
public import LeanShared.Analysis.CompactC1Lipschitz
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Actual smooth transitions of two genuine charts have global compact
smooth Lipschitz representatives on every compact overlap. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ChartTransitionGlobalization
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  (e f : OpenPartialHomeomorph M E)
  (he : e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf : f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)

include he hf in
theorem exists_extension {K : Set E} (compact : IsCompact K)
    (inside : K⊆(e.symm.trans f).source) :
    ∃ G : E → E, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      EqOn G (fun y => f (e.symm y)) K ∧ ∃ L : NNReal, LipschitzWith L G := by
  have smooth : ContDiffOn ℝ ∞ (fun y => f (e.symm y)) (e.symm.trans f).source := by
    intro y hy
    have source : y∈e.target ∧ e.symm y∈f.source := hy
    exact (((contMDiffAt_of_mem_maximalAtlas hf source.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas he source.1)).contDiffAt).contDiffWithinAt
  obtain ⟨G,hG,compactG,agree⟩ := CompactSmoothExtension.exists_compact_extension
    (fun y => f (e.symm y)) compact (e.symm.trans f).open_source inside smooth
  obtain ⟨L,lip⟩ := CompactC1Lipschitz.exists_lipschitz G (hG.of_le (by simp)) compactG
  exact ⟨G,hG,compactG,agree,L,lip⟩
end LeanShared.ChartTransitionGlobalization
