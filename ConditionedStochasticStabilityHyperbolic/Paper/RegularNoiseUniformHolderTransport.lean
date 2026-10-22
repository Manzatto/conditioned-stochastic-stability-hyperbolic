module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCoordinateBounds
public import LeanShared.Geometry.ChartMapMetricCapture
public import LeanShared.Geometry.ControlledChartWeightedTransport

/-! The actual scale-dependent noise maps admit uniformly bounded
weighted lower-Hölder chart transports. The window, coordinate cutoffs,
and bound are constructed from literal Whitney controls. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared

theorem Maps.exists_uniform_holder_transport
    {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T:M≃ₜM} {r:ℝ} (F:Maps (E:=E) (ι:=ι) T r) (hr:1≤r)
    (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (e f:OpenPartialHomeomorph M E)
    (he:e∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hf:f∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (θ:M→ℂ) (smoothθ:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
    (compactθ:HasCompactSupport θ) (supportθ:tsupport θ⊆e.source)
    (K:Set E) (compactK:IsCompact K) (targetK:K⊆f.target)
    {w:M→ℂ} {u a:ℝ} (hu:0<u) (hu1:u<1)
    (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
    (ha:0≤a) (hau:a<u) :
    ∃η:NNReal,0<η ∧ ∃C:ℝ,0≤C ∧
      ∃Q:∀ ε:NNReal,0<ε→ε≤η→cube (ι:=ι) ε→
        (BoundedHolderSpace.graph E a→L[ℂ]BoundedHolderSpace.graph E a),
      (∀ ε hp hl control,‖Q ε hp hl control‖≤C) ∧
      ∀ ε hp hl control (v:BoundedHolderSpace.graph E a),
        (∀ z∉K,BoundedHolderSpace.physical E a v z=0)→∀ y:E,
        BoundedHolderSpace.physical E a (Q ε hp hl control v) y=
          ChartLocalization.coordinate e θ
            (fun x=>w x*SupportedChartExtension.function f
              (BoundedHolderSpace.physical E a v) (F.family ε control.val x)) y := by
  classical
  obtain ⟨ρ,σ,hρ,hσ,cρ,cσ,oneσ,δ,hδ,valid,capture⟩:=
    ChartMapMetricCapture.exists_cutoffs e f θ compactθ supportθ compactK targetK (⟨T,T.continuous⟩:C(M,M))
  have refValid:tsupport σ⊆ChartMapC1Globalization.domain e f T:=
    valid (⟨T,T.continuous⟩:C(M,M)) (by intro x;simpa using hδ.le)
  obtain ⟨ηj,hηj,B,D,hB,hD,bound⟩:=F.uniform_coordinate_bounds hr hT e f he hf
    (tsupport σ) cσ refValid
  let η₀:NNReal:=⟨δ/F.constant,(div_pos hδ F.constant_positive).le⟩
  let η:NNReal:=min F.window (min η₀ ηj)
  have hη:0<η:=lt_min F.window_positive (lt_min (show 0<η₀ from div_pos hδ F.constant_positive) hηj)
  let A:=Σ ε:{ε:NNReal//0<ε∧ε≤η},cube (ι:=ι) ε.val
  let maps:A→M→M:=fun q=>F.family q.1.val q.2.val
  have win(q:A):q.1.val≤F.window:=q.1.property.2.trans (min_le_left _ _)
  have regular(q:A):ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps q):=by
    apply (F.map_regular q.1.val q.1.property.1 (win q) q.2).differentiable.of_le
    exact_mod_cast (Nat.le_floor (by simpa using hr) : (1:ℕ)≤⌊r⌋₊)
  let cmaps(q:A):C(M,M):=⟨maps q,(regular q).continuous⟩
  have close(q:A):∀x,dist (cmaps q x) (T x)≤δ:=by
    intro x
    have hwit:dist (maps q x) (T x)≤F.constant*‖q.2.val‖:=
      (F.whitney_bound q.1.val q.1.property.1 (win q) q.2).uniform x
    have small:(q.1.val:ℝ)≤δ/F.constant:=
      q.1.property.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    have prod:F.constant*(q.1.val:ℝ)≤δ:=by
      have h: (q.1.val:ℝ)*F.constant≤δ:=(le_div_iff₀ F.constant_positive).mp small
      simpa only [mul_comm] using h
    exact hwit.trans ((mul_le_mul_of_nonneg_left
      (NoiseCubeRescaling.cube_norm_le q.1.val q.1.val.coe_nonneg q.2) F.constant_positive.le).trans prod)
  have coordRegular(q:A):ContDiffOn ℝ 1 (fun y=>f (maps q (e.symm y)))
      (ChartMapC1Globalization.domain e f (maps q)):=by
    intro y hy
    have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 e.symm y:=
      (contMDiffAt_symm_of_mem_maximalAtlas he hy.1).of_le (by simp)
    have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f (maps q (e.symm y)):=
      (contMDiffAt_of_mem_maximalAtlas hf hy.2).of_le (by simp)
    exact (last.comp y ((regular q).contMDiffAt.comp y first)).contDiffAt.contDiffWithinAt
  have controls(q:A)(x:E)(hx:x∈tsupport σ):
      ‖f (maps q (e.symm x))‖≤B ∧ ‖fderiv ℝ (fun y=>f (maps q (e.symm y))) x‖≤D:=
    bound q.1.val q.1.property.1
      (q.1.property.2.trans ((min_le_right _ _).trans (min_le_right _ _))) q.2 x hx
  obtain ⟨C,hC,Q,hQ,formula⟩:=ControlledChartWeightedTransport.exists_uniform_transport
    e f he θ smoothθ compactθ supportθ maps ρ σ hρ hσ cρ cσ oneσ
    (fun q=>valid (cmaps q) (close q)) (fun q=>capture (cmaps q) (close q))
    (fun q=>ChartMapC1Globalization.domain_open e f (maps q) (regular q))
    coordRegular hB hD controls hu hu1 hw ha hau
  refine ⟨η,hη,C,hC,(fun ε hp hl control=>Q ⟨⟨ε,hp,hl⟩,control⟩),?_,?_⟩
  · intro ε hp hl control
    exact hQ ⟨⟨ε,hp,hl⟩,control⟩
  · intro ε hp hl control
    exact formula ⟨⟨ε,hp,hl⟩,control⟩
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
