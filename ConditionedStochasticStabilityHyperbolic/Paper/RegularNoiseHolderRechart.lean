module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformFirstHolder
public import LeanShared.Analysis.UniformHolderDerivativeComposition
public import LeanShared.Geometry.ChartRechartDerivative
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-! Quantitative transport of actual Whitney one-jet bounds to fixed smooth
charts. A common noise window and image capture are constructed from the
reference image, rather than assumed for the random maps. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set Filter IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

omit [FiniteDimensional ℝ E] in
private theorem fixed_jet_bound {a:ℝ} (ha:0<a) (ha1:a<1) {f:E→E} {K:Set E}
    (compact:IsCompact K) (smooth:∀x∈K,ContDiffAt ℝ 2 f x) :
    ∃B C:ℝ,0≤B ∧ 0≤C ∧ (∀x∈K,‖fderiv ℝ f x‖≤B) ∧
      ∀x∈K,∀y∈K,‖fderiv ℝ f x-fderiv ℝ f y‖≤C*‖x-y‖^a :=by
  have continuousD:ContinuousOn (fderiv ℝ f) K:=fun x hx=>
    ((smooth x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨B,hB,boundB⟩:=(compact.image_of_continuousOn continuousD).isBounded.exists_pos_norm_le
  obtain ⟨C,hC,boundC⟩:=LeanShared.CompactLocalHolder.bound_on_compact ha ha1.le compact
    (fderiv ℝ f) (fun x hx=>by
      obtain ⟨U,openU,inU,D,hD,bound⟩:=(LeanShared.LocalOneHolderJet.of_contDiffAt_two ha1.le (smooth x hx)).2
      exact ⟨U,openU,inU,D,hD,fun y hy z hz=>by simpa only [dist_eq_norm] using bound y hy z hz⟩)
  exact ⟨B,C,hB.le,hC,(fun x hx=>boundB _ ⟨x,hx,rfl⟩),fun x hx y hy=>by
    simpa only [dist_eq_norm] using boundC x hx y hy⟩

omit [FiniteDimensional ℝ E] in
private theorem transition_c2 (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x:E) (source:x∈c.target) (target:c.symm x∈d.source) :
    ContDiffAt ℝ 2 (d∘c.symm) x :=by
  exact ((contMDiffAt_of_mem_maximalAtlas hd target).comp x
    (contMDiffAt_symm_of_mem_maximalAtlas hc source)).contDiffAt.of_le (by simp)

omit [FiniteDimensional ℝ E] in
private theorem coordinate_c1 {f:M→M} (smooth:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x:E) (source:x∈c.target) (target:f (c.symm x)∈d.source) :
    ContDiffAt ℝ 1 (d∘f∘c.symm) x :=by
  have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm x:=
    (contMDiffAt_symm_of_mem_maximalAtlas hc source).of_le (by simp)
  have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d (f (c.symm x)):=
    (contMDiffAt_of_mem_maximalAtlas hd target).of_le (by simp)
  exact (last.comp x (smooth.contMDiffAt.comp x first)).contDiffAt

omit [FiniteDimensional ℝ E] in
theorem Maps.uniform_first_holder_rechart {T:M≃ₜM} {r a:ℝ}
    (F:Maps (E:=E) (ι:=ι) T r) (ha:0<a) (ha1:a<1) (lower:a+1<r)
    (regular:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) r T)
    (i:Fin F.atlas.count) (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    {K L V:Set E} (compactK:IsCompact K) (convexK:Convex ℝ K)
    (compactL:IsCompact L) (convexL:Convex ℝ L) (insideL:L⊆F.atlas.coordinatePatch i)
    (compactV:IsCompact V)
    (sourceK:∀x∈K,x∈c.target ∧ c.symm x∈(F.atlas.source i).source)
    (mapsA:(F.atlas.source i∘c.symm) '' K⊆L)
    (targetV:∀y∈V,y∈(F.atlas.target i).target ∧ (F.atlas.target i).symm y∈d.source)
    (reference:(F.atlas.coordinate T i) '' L⊆interior V) :
    ∃η:NNReal,0<η ∧ η≤F.window ∧∃B C:ℝ,0≤B ∧ 0≤C ∧
      ∀ε:NNReal,0<ε→ε≤η→∀control:cube (ι:=ι) ε,
        (∀x∈K,‖fderiv ℝ (d∘F.family ε control.val∘c.symm) x‖≤B) ∧
        ∀x∈K,∀y∈K,
          ‖fderiv ℝ (d∘F.family ε control.val∘c.symm) x-
            fderiv ℝ (d∘F.family ε control.val∘c.symm) y‖≤C*‖x-y‖^a :=by
  let A:E→E:=F.atlas.source i∘c.symm
  let H:E→E:=d∘(F.atlas.target i).symm
  have smoothA:∀x∈K,ContDiffAt ℝ 2 A x:=fun x hx=>transition_c2 c (F.atlas.source i)
    hc (F.atlas.source_smooth i) x (sourceK x hx).1 (sourceK x hx).2
  have smoothH:∀y∈V,ContDiffAt ℝ 2 H y:=fun y hy=>transition_c2 (F.atlas.target i) d
    (F.atlas.target_smooth i) hd y (targetV y hy).1 (targetV y hy).2
  obtain ⟨BA,CA,hBA,hCA,valueA,holderA⟩:=fixed_jet_bound ha ha1 compactK smoothA
  obtain ⟨BH,CH,hBH,hCH,valueH,holderH⟩:=fixed_jet_bound ha ha1 compactV smoothH
  obtain ⟨BF,CF,hBF,hCF,boundF⟩:=F.uniform_first_holder_bounds ha ha1 lower regular i compactL convexL insideL
  have one:1≤⌊r⌋₊:=Nat.le_floor (by simpa using (show (1:ℝ)≤r by linarith))
  have regularT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T:=regular.differentiable.of_le (by exact_mod_cast one)
  have refC1:∀x∈L,ContDiffAt ℝ 1 (F.atlas.coordinate T i) x:=by
    intro x hx
    exact coordinate_c1 regularT _ _ (F.atlas.source_smooth i) (F.atlas.target_smooth i) x
      (insideL hx).1 (F.atlas.deterministic_target i ⟨_,subset_closure (insideL hx).2,rfl⟩)
  have compactImage:IsCompact ((F.atlas.coordinate T i) '' L):=
    compactL.image_of_continuousOn (fun x hx=>(refC1 x hx).continuousAt.continuousWithinAt)
  obtain ⟨δ,hδ,tube⟩:=compactImage.exists_cthickening_subset_open isOpen_interior reference
  let η:NNReal:=min F.window ⟨δ/F.constant,(div_pos hδ F.constant_positive).le⟩
  have hη:0<η:=lt_min F.window_positive (show (0:NNReal)<⟨δ/F.constant,(div_pos hδ F.constant_positive).le⟩ from div_pos hδ F.constant_positive)
  refine ⟨η,hη,min_le_left _ _,BH*(BF*BA),
    CH*(BF*BA)^a*(BF*BA)+BH*(CF*BA^a*BA+BF*CA),by positivity,by positivity,?_⟩
  intro ε hp hw control
  have window:ε≤F.window:=hw.trans (min_le_left _ _)
  let f:=F.atlas.coordinate (F.family ε control.val) i
  have regularF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (F.family ε control.val):=
    (F.map_regular ε hp window control).differentiable.of_le (by exact_mod_cast one)
  have smoothF:∀x∈L,ContDiffAt ℝ 1 f x:=by
    intro x hx
    exact coordinate_c1 regularF _ _ (F.atlas.source_smooth i) (F.atlas.target_smooth i) x
      (insideL hx).1 ((F.whitney_bound ε hp window control).target_control i ⟨_,subset_closure (insideL hx).2,rfl⟩)
  have captured:f '' L⊆V:=by
    rintro _ ⟨x,hx,rfl⟩
    apply interior_subset (tube (Metric.mem_cthickening_of_dist_le _ _ δ _ ⟨x,hx,rfl⟩ _))
    rw [dist_eq_norm]
    have bound:=(F.whitney_bound ε hp window control).derivatives i 0 (by omega) x (insideL hx)
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,LinearIsometryEquiv.norm_map] at bound
    have small:(ε:ℝ)≤δ/F.constant:=hw.trans (min_le_right _ _)
    exact bound.trans ((mul_le_mul_of_nonneg_left
      (LeanShared.NoiseCubeRescaling.cube_norm_le (ε:ℝ) ε.property control) F.constant_positive.le).trans
        (by have h: (ε:ℝ)*F.constant≤δ:=(le_div_iff₀ F.constant_positive).mp small
            simpa only [mul_comm] using h))
  have first:=LeanShared.UniformHolderDerivativeComposition.bound convexK mapsA
    (fun x hx=>(smoothF x hx).differentiableAt (by norm_num))
    (fun x hx=>(smoothA x hx).differentiableAt (by norm_num)) ha.le hBF hBA hCF hCA
    (boundF ε hp window control).1 valueA (boundF ε hp window control).2 holderA
  have mapsSecond:(f∘A) '' K⊆V:=by
    rintro _ ⟨x,hx,rfl⟩
    exact captured ⟨A x,mapsA ⟨x,hx,rfl⟩,rfl⟩
  have second:=LeanShared.UniformHolderDerivativeComposition.bound convexK mapsSecond
    (fun x hx=>(smoothH x hx).differentiableAt (by norm_num))
    (fun x hx=>((smoothF (A x) (mapsA ⟨x,hx,rfl⟩)).differentiableAt (by norm_num)).comp x
      ((smoothA x hx).differentiableAt (by norm_num))) ha.le hBH (mul_nonneg hBF hBA) hCH
    (by positivity : 0≤CF*BA^a*BA+BF*CA) valueH first.1 holderH first.2
  have identity:∀x∈K,fderiv ℝ (d∘F.family ε control.val∘c.symm) x=fderiv ℝ (H∘(f∘A)) x:=by
    intro x hx
    apply LeanShared.ChartRechartDerivative.fderiv_eq c d (F.atlas.source i) (F.atlas.target i)
      regularF.continuous (sourceK x hx).1 (sourceK x hx).2
    have ax:A x∈L:=mapsA ⟨x,hx,rfl⟩
    have target: F.family ε control.val ((F.atlas.source i).symm (A x))∈(F.atlas.target i).source:=
      (F.whitney_bound ε hp window control).target_control i ⟨_,subset_closure (insideL ax).2,rfl⟩
    have inverse:(F.atlas.source i).symm (A x)=c.symm x:=(F.atlas.source i).left_inv (sourceK x hx).2
    rw [inverse] at target
    exact target
  exact ⟨fun x hx=>by rw [identity x hx];exact second.1 x hx,
    fun x hx y hy=>by rw [identity x hx,identity y hy];exact second.2 x hx y hy⟩
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
