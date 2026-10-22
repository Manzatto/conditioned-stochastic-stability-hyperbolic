module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseHolderRechart
import Mathlib.Tactic

/-! Local quantitative first-jet bounds in ANY fixed genuine charts.
All auxiliary compact domains and the common noise window are selected
internally from the reference map and the actual covering Whitney atlas. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set Filter IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem small_closedBall {x:E} {U:Set E} (near:U∈𝓝 x) :
    ∃δ:ℝ,0<δ ∧ Metric.closedBall x δ⊆U :=by
  obtain ⟨ε,hε,ball⟩:=Metric.mem_nhds_iff.mp near
  exact ⟨ε/2,half_pos hε,(Metric.closedBall_subset_ball (half_lt_self hε)).trans ball⟩

theorem Maps.local_first_holder_bounds {T:M≃ₜM} {r a:ℝ}
    (F:Maps (E:=E) (ι:=ι) T r) (ha:0<a) (ha1:a<1) (lower:a+1<r)
    (regular:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) r T)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x:E) (source:x∈c.target) (target:T (c.symm x)∈d.source) :
    ∃δ:ℝ,0<δ ∧∃η:NNReal,0<η ∧ η≤F.window ∧∃B C:ℝ,0≤B ∧ 0≤C ∧
      ∀ε:NNReal,0<ε→ε≤η→∀control:cube (ι:=ι) ε,
        (∀y∈Metric.closedBall x δ,‖fderiv ℝ (d∘F.family ε control.val∘c.symm) y‖≤B) ∧
        ∀y∈Metric.closedBall x δ,∀z∈Metric.closedBall x δ,
          ‖fderiv ℝ (d∘F.family ε control.val∘c.symm) y-
            fderiv ℝ (d∘F.family ε control.val∘c.symm) z‖≤C*‖y-z‖^a :=by
  let m:=c.symm x
  have covered:m∈⋃i,F.atlas.patch i:=by rw [F.atlas.patch_cover];exact mem_univ _
  obtain ⟨i,inPatch⟩:=mem_iUnion.mp covered
  let e:=F.atlas.source i
  let h:=F.atlas.target i
  let z:=e m
  let y:=h (T m)
  have inSource:m∈e.source:=F.atlas.patch_source i (subset_closure inPatch)
  have inTarget:T m∈h.source:=F.atlas.deterministic_target i ⟨m,subset_closure inPatch,rfl⟩
  have invz:e.symm z=m:=e.left_inv inSource
  have invy:h.symm y=T m:=h.left_inv inTarget
  have nearV:h.target∩h.symm ⁻¹' d.source∈𝓝 y:=by
    apply inter_mem (h.open_target.mem_nhds (h.map_source inTarget))
    apply (h.continuousAt_symm (h.map_source inTarget)).preimage_mem_nhds
    rw [invy]
    exact d.open_source.mem_nhds target
  obtain ⟨rV,hrV,subV⟩:=small_closedBall nearV
  let V:=Metric.closedBall y rV
  have targetV:∀q∈V,q∈h.target ∧ h.symm q∈d.source:=fun q hq=>subV hq
  have lowerRegular:=LeanShared.FractionalOneJetLowering.regular_one_add ha ha1 lower regular
  have referenceC1:ContDiffAt ℝ 1 (F.atlas.coordinate T i) z:=
    (lowerRegular.one_jet_in_charts ha ha1 e h (F.atlas.source_smooth i)
      (F.atlas.target_smooth i) z (e.map_source inSource) (by rw [invz];exact inTarget)).1
  have referenceValue:F.atlas.coordinate T i z=y:=by
    change h (T (e.symm z))=y
    rw [invz]
  have nearReference:(F.atlas.coordinate T i) ⁻¹' Metric.ball y rV∈𝓝 z:=
    referenceC1.continuousAt.preimage_mem_nhds (by rw [referenceValue];exact Metric.ball_mem_nhds _ hrV)
  have nearPatch:F.atlas.coordinatePatch i∈𝓝 z:=by
    apply inter_mem (e.open_target.mem_nhds (e.map_source inSource))
    apply (e.continuousAt_symm (e.map_source inSource)).preimage_mem_nhds
    rw [invz]
    exact (F.atlas.patch_open i).mem_nhds inPatch
  obtain ⟨rL,hrL,subL⟩:=small_closedBall (inter_mem nearPatch nearReference)
  let L:=Metric.closedBall z rL
  have insideL:L⊆F.atlas.coordinatePatch i:=fun q hq=>(subL hq).1
  have reference:(F.atlas.coordinate T i) '' L⊆interior V:=by
    rintro _ ⟨q,hq,rfl⟩
    exact Metric.ball_subset_interior_closedBall (subL hq).2
  let A:E→E:=e∘c.symm
  have continuousA:ContinuousAt A x:=
    (e.continuousAt inSource).comp (c.continuousAt_symm source)
  have valueA:A x=z:=rfl
  have nearA:A ⁻¹' Metric.ball z rL∈𝓝 x:=continuousA.preimage_mem_nhds
    (by rw [valueA];exact Metric.ball_mem_nhds _ hrL)
  have nearSource:c.target∩c.symm ⁻¹' e.source∈𝓝 x:=inter_mem (c.open_target.mem_nhds source)
    ((c.continuousAt_symm source).preimage_mem_nhds (e.open_source.mem_nhds inSource))
  obtain ⟨δ,hδ,subK⟩:=small_closedBall (inter_mem nearSource nearA)
  let K:=Metric.closedBall x δ
  have sourceK:∀q∈K,q∈c.target ∧ c.symm q∈e.source:=fun q hq=>(subK hq).1
  have mapsA:A '' K⊆L:=by
    rintro _ ⟨q,hq,rfl⟩
    exact Metric.ball_subset_closedBall (subK hq).2
  obtain ⟨η,hη,window,B,C,hB,hC,bound⟩:=F.uniform_first_holder_rechart ha ha1 lower regular i c d hc hd
    (isCompact_closedBall _ _) (convex_closedBall _ _) (isCompact_closedBall _ _) (convex_closedBall _ _)
    insideL (isCompact_closedBall _ _) sourceK mapsA targetV reference
  exact ⟨δ,hδ,η,hη,window,B,C,hB,hC,bound⟩
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
