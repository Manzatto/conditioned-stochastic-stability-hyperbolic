module
public import LeanShared.Geometry.FractionalChartOneJet
public import LeanShared.Analysis.CompactLocalHolder

/-! Actual manifold C^(1+a) gives quantitative derivative value and Holder
bounds on every compact valid coordinate domain. Both constants are proved. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M N:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem Regular.compact_one_holder_in_charts {a:ℝ} (ha:0<a) (ha1:a<1) {f:M→N}
    (regular:Regular (E:=E) (F:=F) (a+1) f)
    (c:OpenPartialHomeomorph M E) (d:OpenPartialHomeomorph N F)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,F)) ∞ N)
    {K:Set E} (compact:IsCompact K) (valid:∀y∈K,y∈c.target ∧ f (c.symm y)∈d.source) :
    ∃B C:ℝ,0≤B ∧ 0≤C ∧ (∀y∈K,‖fderiv ℝ (d∘f∘c.symm) y‖≤B) ∧
      ∀y∈K,∀z∈K,‖fderiv ℝ (d∘f∘c.symm) y-fderiv ℝ (d∘f∘c.symm) z‖≤C*‖y-z‖^a :=by
  have jets:∀y∈K,LocalOneHolderJet.At a (d∘f∘c.symm) y:=fun y hy=>
    regular.one_jet_in_charts ha ha1 c d hc hd y (valid y hy).1 (valid y hy).2
  have continuousD:ContinuousOn (fderiv ℝ (d∘f∘c.symm)) K:=fun y hy=>
    ((jets y hy).1.continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨B,hB,boundB⟩:=(compact.image_of_continuousOn continuousD).isBounded.exists_pos_norm_le
  obtain ⟨C,hC,boundC⟩:=CompactLocalHolder.bound_on_compact ha ha1.le compact
    (fderiv ℝ (d∘f∘c.symm)) (fun y hy=>by
      obtain ⟨U,openU,inU,D,hD,bound⟩:=(jets y hy).2
      exact ⟨U,openU,inU,D,hD,fun z hz w hw=>by
        simpa only [dist_eq_norm] using bound z hz w hw⟩)
  refine ⟨B,C,hB.le,hC,(fun y hy=>boundB _ ⟨y,hy,rfl⟩),?_⟩
  intro y hy z hz
  simpa only [dist_eq_norm] using boundC y hy z hz
end LeanShared.FractionalManifoldRegularity
