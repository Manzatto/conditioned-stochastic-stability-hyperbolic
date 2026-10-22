module
public import LeanShared.Analysis.CompactC1Extension
public import LeanShared.Analysis.CompactC1Lipschitz
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Literal coordinates of a C¹ manifold map have global compact C¹
Lipschitz representatives on each compact valid chart domain. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ChartMapC1Globalization
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  (e f:OpenPartialHomeomorph M E)
  (he:e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf:f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)

@[expose] def domain : Set E := e.target ∩ (fun y=>F (e.symm y)) ⁻¹' f.source

include hF in
omit [FiniteDimensional ℝ E] in
theorem domain_open : IsOpen (domain e f F) :=
  (hF.continuous.comp_continuousOn e.continuousOn_symm).isOpen_inter_preimage
    e.open_target f.open_source

include he hf hF in
theorem exists_extension {K:Set E} (compact:IsCompact K) (inside:K⊆domain e f F) :
    ∃G:E→E,ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      EqOn G (fun y=>f (F (e.symm y))) K ∧ ∃L:NNReal,LipschitzWith L G := by
  have regular : ContDiffOn ℝ 1 (fun y=>f (F (e.symm y))) (domain e f F) := by
    intro y hy
    have inverse : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 e.symm y :=
      (contMDiffAt_symm_of_mem_maximalAtlas he hy.1).of_le (by simp)
    have forward : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f (F (e.symm y)) :=
      (contMDiffAt_of_mem_maximalAtlas hf hy.2).of_le (by simp)
    exact (forward.comp y (hF.contMDiffAt.comp y inverse)).contDiffAt.contDiffWithinAt
  obtain ⟨G,hG,cG,agree⟩ := CompactC1Extension.exists_compact_extension
    (fun y=>f (F (e.symm y))) compact (domain_open e f F hF) inside regular
  obtain ⟨L,lip⟩ := CompactC1Lipschitz.exists_lipschitz G hG cG
  exact ⟨G,hG,cG,agree,L,lip⟩
end LeanShared.ChartMapC1Globalization
