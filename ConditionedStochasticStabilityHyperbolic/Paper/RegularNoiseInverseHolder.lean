module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLocalFirstHolder
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseDerivativeBound
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformCapture
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseChartInverseGerms
public import LeanShared.Analysis.InverseDerivativeHolder
import Mathlib.Tactic

/-! Actual local C^(1+a) inverse-noise controls from the literal forward
Whitney assumptions. All inverse derivative bounds, inverse chart capture
and Holder constants are derived on one common positive noise window. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set Filter IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]

theorem InverseFamily.local_jet_controls {T:M≃ₜM} {r a:ℝ} {F:Maps (E:=E) (ι:=ι) T r}
    (J:InverseFamily F) (ha:0<a) (ha1:a<1) (lower:a+1<r)
    (regular:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) r T)
    (inverse:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y:E) (inside:y∈d.target) (target:T.symm (d.symm y)∈c.source) :
    ∃δ:ℝ,0<δ ∧∃η:NNReal,0<η ∧ η≤J.window ∧∃B0 B1 H:ℝ,0≤B0 ∧ 0≤B1 ∧ 0≤H ∧
      ∀ε:NNReal,0<ε→ε≤η→∀control:cube (ι:=ι) ε,
        let g:=c∘(fun x=>J.map ε (control.val,x))∘d.symm
        (∀q∈Metric.closedBall y δ,ContDiffAt ℝ 1 g q ∧ ‖g q‖≤B0 ∧ ‖fderiv ℝ g q‖≤B1) ∧
        ∀q∈Metric.closedBall y δ,∀z∈Metric.closedBall y δ,
          ‖fderiv ℝ g q-fderiv ℝ g z‖≤H*‖q-z‖^a :=by
  let p:=T.symm (d.symm y)
  let z:=c p
  have one:1≤⌊r⌋₊:=Nat.le_floor (by simpa using (show (1:ℝ)≤r by linarith))
  have regularT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T:=regular.differentiable.of_le (by exact_mod_cast one)
  have forwardTarget:T (c.symm z)∈d.source:=by
    rw [c.left_inv target,T.apply_symm_apply]
    exact d.map_target inside
  obtain ⟨δF,hδF,ηF,hηF,windowF,BF,CF,hBF,hCF,boundF⟩:=F.local_first_holder_bounds ha ha1 lower regular
    c d hc hd z (c.map_source target) forwardTarget
  let U:=c.source∩c ⁻¹' Metric.ball z δF
  have openU:IsOpen U:=c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
  have inU:p∈U:=⟨target,Metric.mem_ball_self hδF⟩
  have near:(T.symm∘d.symm) ⁻¹' U∈𝓝 y:=
    (T.symm.continuous.continuousAt.comp (d.continuousAt_symm inside)).preimage_mem_nhds
      (openU.mem_nhds inU)
  obtain ⟨R,hR,ball⟩:=Metric.mem_nhds_iff.mp (inter_mem (d.open_target.mem_nhds inside) near)
  let δ:=R/2
  have hδ:0<δ:=half_pos hR
  let K:=Metric.closedBall y δ
  have subK:K⊆d.target∩(T.symm∘d.symm) ⁻¹' U:=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans ball
  have sourceK:K⊆d.target:=fun q hq=>(subK hq).1
  have validK:K⊆d.target∩(T.symm∘d.symm) ⁻¹' c.source:=fun q hq=>⟨(subK hq).1,(subK hq).2.1⟩
  have compactStarts:IsCompact (d.symm '' K):=(isCompact_closedBall y δ).image_of_continuousOn
    (d.continuousOn_symm.mono sourceK)
  obtain ⟨ηC,hηC,windowC,capture⟩:=J.exists_uniform_target (d.symm '' K) U compactStarts openU
    (by rintro _ ⟨q,hq,rfl⟩;exact (subK hq).2)
  obtain ⟨ηM,hηM,windowM,M,hM,boundM⟩:=J.uniform_chart_derivative_bound (by linarith) regularT inverse c d hc hd
    (isCompact_closedBall y δ) validK
  let η:=min ηF (min ηC ηM)
  have hη:0<η:=lt_min hηF (lt_min hηC hηM)
  refine ⟨δ,hδ,η,hη,((min_le_right _ _).trans (min_le_right _ _)).trans windowM,
    ‖z‖+δF,M,M*CF*M^a*M,by positivity,hM,by positivity,?_⟩
  intro ε hp hw control
  have wf:ε≤ηF:=hw.trans (min_le_left _ _)
  have wc:ε≤ηC:=hw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have wm:ε≤ηM:=hw.trans ((min_le_right _ _).trans (min_le_right _ _))
  have window:ε≤J.window:=wm.trans windowM
  let f:E→E:=d∘F.family ε control.val∘c.symm
  let g:E→E:=c∘(fun q=>J.map ε (control.val,q))∘d.symm
  have captured:∀q∈K,J.map ε (control.val,d.symm q)∈U:=
    fun q hq=>capture ε hp wc control ⟨q,hq,rfl⟩
  have image:∀q∈K,g q∈Metric.closedBall z δF:=fun q hq=>Metric.ball_subset_closedBall (captured q hq).2
  have smoothG:∀q∈K,ContDiffAt ℝ 1 g q:=by
    intro q hq
    have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm q:=
      (contMDiffAt_symm_of_mem_maximalAtlas hd (sourceK hq)).of_le (by simp)
    have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c (J.map ε (control.val,d.symm q)):=
      (contMDiffAt_of_mem_maximalAtlas hc (captured q hq).1).of_le (by simp)
    exact (last.comp q ((J.map_contMDiff ε hp window control).contMDiffAt.comp q first)).contDiffAt
  have smoothF:∀q∈K,ContDiffAt ℝ 1 f (g q):=by
    intro q hq
    have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm (g q):=
      (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source (captured q hq).1)).of_le (by simp)
    have targetF:F.family ε control.val (c.symm (g q))∈d.source:=by
      rw [show c.symm (g q)=J.map ε (control.val,d.symm q) from c.left_inv (captured q hq).1]
      rw [J.right ε hp window _ (J.contains ε hp window control.property)]
      exact d.map_target (sourceK hq)
    have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d (F.family ε control.val (c.symm (g q))):=
      (contMDiffAt_of_mem_maximalAtlas hd targetF).of_le (by simp)
    have middle:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (F.family ε control.val):=
      (F.map_regular ε hp (wf.trans windowF) control).differentiable.of_le (by exact_mod_cast one)
    exact (last.comp (g q) (middle.contMDiffAt.comp (g q) first)).contDiffAt
  have identities:∀q∈K,(g∘f)=ᶠ[𝓝 (g q)]id ∧ (f∘g)=ᶠ[𝓝 q]id:=fun q hq=>
    J.chart_inverse_germs ε hp window control c d q (sourceK hq) (captured q hq).1
  have holder:=LeanShared.InverseDerivativeHolder.bound (convex_closedBall y δ)
    (fun q hq=>(smoothF q hq).differentiableAt (by norm_num))
    (fun q hq=>(smoothG q hq).differentiableAt (by norm_num))
    (fun q hq=>(identities q hq).1) (fun q hq=>(identities q hq).2) ha.le hM hCF
    (boundM ε hp wm control) (fun q hq v hv=>(boundF ε hp wf control).2 _ (image q hq) _ (image v hv))
  refine ⟨?_,holder⟩
  intro q hq
  refine ⟨smoothG q hq,?_,boundM ε hp wm control q hq⟩
  have distance:‖g q-z‖≤δF:=by simpa only [Metric.mem_closedBall,dist_eq_norm] using image q hq
  exact (norm_le_norm_sub_add (g q) z).trans ((add_le_add distance le_rfl).trans_eq (add_comm _ _))
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
