module
public import LeanShared.Geometry.ChartMapFamilyCapture
public import Mathlib.Topology.ContinuousMap.Compact

/-! Fixed inner/outer chart cutoffs work for EVERY continuous map uniformly
close to a reference map. No continuity of the indexed family is needed. -/
public noncomputable section
open Set Filter IsManifold Metric
open scoped ContDiff Topology
namespace LeanShared.ChartMapMetricCapture
variable {E M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  (e f:OpenPartialHomeomorph M E) (θ:M→ℂ)
  (compactθ:HasCompactSupport θ) (supportθ:tsupport θ⊆e.source)
  {K:Set E} (compactK:IsCompact K) (targetK:K⊆f.target) (T:C(M,M))

include compactθ supportθ compactK targetK in
omit [ChartedSpace E M] in
theorem exists_cutoffs : ∃ρ σ:E→ℝ,ContDiff ℝ ∞ ρ ∧ ContDiff ℝ ∞ σ ∧
    HasCompactSupport ρ ∧ HasCompactSupport σ ∧
    EqOn σ (fun _=>1) (tsupport ρ) ∧ ∃δ:ℝ,0<δ ∧
      (∀G:C(M,M),(∀x,dist (G x) (T x)≤δ)→
        tsupport σ⊆ChartMapC1Globalization.domain e f G) ∧
      (∀G:C(M,M),(∀x,dist (G x) (T x)≤δ)→
        ∀x∈tsupport θ,G x∈f.symm '' K→ρ (e x)=1) := by
  have eval:Continuous (fun z:C(M,M)×M=>z.1 z.2):=continuous_eval
  obtain ⟨ρ,hρ,cρ,O₁,hO₁,hT₁,validρ,capture⟩:=ChartMapFamilyCapture.exists_capture
    e f θ compactθ supportθ compactK targetK (fun G:C(M,M)=>G) eval T
  have openRef:IsOpen (ChartMapC1Globalization.domain e f T):=
    (T.continuous.comp_continuousOn e.continuousOn_symm).isOpen_inter_preimage e.open_target f.open_source
  obtain ⟨σ,hσ,cσ,sσ,_,oneσ⟩:=CompactSmoothCutoff.exists_cutoff cρ openRef (validρ T hT₁)
  let domain:Set (C(M,M)×E):=univ×ˢe.target
  have coordinate:ContinuousOn (fun z:C(M,M)×E=>z.1 (e.symm z.2)) domain:=
    eval.comp_continuousOn (continuousOn_fst.prodMk
      (e.continuousOn_symm.comp continuousOn_snd (fun _ hz=>hz.2)))
  let valid:Set (C(M,M)×E):=domain∩(fun z:C(M,M)×E=>z.1 (e.symm z.2)) ⁻¹' f.source
  have openValid:IsOpen valid:=coordinate.isOpen_inter_preimage (isOpen_univ.prod e.open_target) f.open_source
  have contains:({T}:Set C(M,M))×ˢtsupport σ⊆valid:=by
    rintro ⟨G,y⟩ ⟨hG,hy⟩
    have eqn:G=T:=mem_singleton_iff.mp hG
    subst G
    exact ⟨⟨mem_univ _,(sσ hy).1⟩,(sσ hy).2⟩
  obtain ⟨O₂,Y,hO₂,_,hT₂,hY,tube⟩:=generalized_tube_lemma isCompact_singleton cσ openValid contains
  obtain ⟨δ,hδ,ball⟩:=Metric.mem_nhds_iff.mp ((hO₁.inter hO₂).mem_nhds
    ⟨hT₁,singleton_subset_iff.mp hT₂⟩)
  have near(G:C(M,M))(close:∀x,dist (G x) (T x)≤δ/2):G∈O₁∩O₂:=by
    apply ball
    rw [Metric.mem_ball]
    have hdist:dist G T≤δ/2:=(ContinuousMap.dist_le (by linarith)).mpr close
    linarith
  refine ⟨ρ,σ,hρ,hσ,cρ,cσ,oneσ,δ/2,by linarith,?_,?_⟩
  · intro G hG y hy
    have h:=tube (show (G,y)∈O₂×ˢY from ⟨(near G hG).2,hY hy⟩)
    exact ⟨h.1.2,h.2⟩
  · intro G hG
    exact capture G (near G hG).1
end LeanShared.ChartMapMetricCapture
