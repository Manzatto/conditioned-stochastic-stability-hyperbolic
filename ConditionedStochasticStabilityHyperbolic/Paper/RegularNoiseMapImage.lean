module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformWeightedHolderBound
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordContinuity
public import Mathlib.Topology.ContinuousMap.Compact

/-! A common metric parameter space for actual small-noise maps and the
reference. It is independent of every Hölder exponent and physical model.
No continuity across ε is imposed. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
open LeanShared
variable {E M ι:Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] {T:M≃ₜM} {r:ℝ} (F:Maps (E:=E) (ι:=ι) T r)
  (hr:1≤r) (η:NNReal) (hw:η≤F.window)

@[expose] def Parameter := Option (Σ ε:{ε:NNReal//0<ε∧ε≤η},cube (ι:=ι) ε.val)
@[expose] def parameterMaps : Parameter (ι:=ι) η→M→M
  | none=>T
  | some a=>F.family a.1.val a.2.val

include hr hw in
omit [CompactSpace M] in
theorem parameter_continuous (a:Parameter (ι:=ι) η) : Continuous (parameterMaps F η a) := by
  cases a with
  | none=>exact T.continuous
  | some a=>exact (F.contMDiff_one hr a.1.val a.1.property.1 (a.1.property.2.trans hw) a.2).continuous

@[expose] def continuousMaps (a:Parameter (ι:=ι) η) : C(M,M):=
  ⟨parameterMaps F η a,parameter_continuous F hr η hw a⟩
@[expose] def Space := Set.range (continuousMaps F hr η hw)
@[expose] def ofParameter (a:Parameter (ι:=ι) η) : Space F hr η hw:=
  ⟨continuousMaps F hr η hw a,mem_range_self a⟩
@[expose] def maps (a:Space F hr η hw) : M→M:=a.val

def representative (a:Space F hr η hw) : Parameter (ι:=ι) η:=Classical.choose a.property

omit [CompactSpace M] in
theorem representative_maps (a:Space F hr η hw) :
    parameterMaps F η (representative F hr η hw a)=maps F hr η hw a :=
  congrArg (fun f:C(M,M)=>(f:M→M)) (Classical.choose_spec a.property)

omit [CompactSpace M] in
theorem regular (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T) (a:Space F hr η hw) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps F hr η hw a) := by
  have h:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1
      (parameterMaps F η (representative F hr η hw a)):=by
    cases representative F hr η hw a with
    | none=>exact hT
    | some a=>exact F.contMDiff_one hr a.1.val a.1.property.1 (a.1.property.2.trans hw) a.2
  exact representative_maps F hr η hw a ▸ h

@[expose] def reference : Space F hr η hw:=ofParameter F hr η hw none
@[expose] def noise (ε:NNReal) (hp:0<ε) (hl:ε≤η) (control:cube (ι:=ι) ε) : Space F hr η hw:=
  ofParameter F hr η hw (some ⟨⟨ε,hp,hl⟩,control⟩)

theorem evaluation_continuous : Continuous (fun z:Space F hr η hw×M=>maps F hr η hw z.1 z.2) := by
  exact continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

omit [CompactSpace M] in
theorem noise_continuous (ε:NNReal) (hp:0<ε) (hl:ε≤η) :
    Continuous (noise F hr η hw ε hp hl) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact F.cube_map_continuous ε hp (hl.trans hw)

theorem noise_proximity (ε:NNReal) (hp:0<ε) (hl:ε≤η) (control:cube (ι:=ι) ε) :
    dist (noise F hr η hw ε hp hl control) (reference F hr η hw)≤F.constant*(ε:ℝ) := by
  change dist (continuousMaps F hr η hw (some ⟨⟨ε,hp,hl⟩,control⟩)) (continuousMaps F hr η hw none)≤_
  apply (ContinuousMap.dist_le (mul_nonneg F.constant_positive.le ε.coe_nonneg)).mpr
  intro x
  exact ((F.whitney_bound ε hp (hl.trans hw) control).uniform x).trans
    (mul_le_mul_of_nonneg_left (NoiseCubeRescaling.cube_norm_le ε ε.coe_nonneg control) F.constant_positive.le)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
