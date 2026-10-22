module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWhitneyFirstHolderBounds
public import LeanShared.Geometry.FractionalOneJetLowering
public import LeanShared.Analysis.SecondDerivativeTensorNorm
public import LeanShared.Analysis.BoundedHolderLowering
import Mathlib.Tactic

/-! Actual uniform C^(1+a) coordinate control for every manuscript r>1.
The fractional Whitney seminorm handles r<2, while the literal second-jet
Whitney bound and convex mean value estimate handle r>=2. -/
public noncomputable section
open Set IsManifold
open scoped NNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

omit [FiniteDimensional ℝ E] in
private theorem coordinate_c2 {f:M→M} (smooth:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 2 f)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x:E) (source:x∈c.target) (target:f (c.symm x)∈d.source) :
    ContDiffAt ℝ 2 (d∘f∘c.symm) x :=by
  have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 2 c.symm x:=
    (contMDiffAt_symm_of_mem_maximalAtlas hc source).of_le (by simp)
  have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 2 d (f (c.symm x)):=
    (contMDiffAt_of_mem_maximalAtlas hd target).of_le (by simp)
  exact (last.comp x (smooth.contMDiffAt.comp x first)).contDiffAt

omit [FiniteDimensional ℝ E] in
theorem Maps.uniform_first_holder_bounds {T:M≃ₜM} {r a:ℝ}
    (F:Maps (E:=E) (ι:=ι) T r) (ha:0<a) (ha1:a<1) (lower:a+1<r)
    (regular:LeanShared.FractionalManifoldRegularity.Regular (E:=E) (F:=E) r T)
    (i:Fin F.atlas.count) {K:Set E} (compact:IsCompact K) (convex:Convex ℝ K)
    (inside:K⊆F.atlas.coordinatePatch i) :
    ∃B C:ℝ,0≤B ∧ 0≤C ∧∀ε:NNReal,0<ε→ε≤F.window→∀control:cube (ι:=ι) ε,
      (∀x∈K,‖fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x‖≤B) ∧
      ∀x∈K,∀y∈K,
        ‖fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) x-
          fderiv ℝ (F.atlas.coordinate (F.family ε control.val) i) y‖≤C*‖x-y‖^a :=by
  by_cases small:r<2
  · obtain ⟨B,C,hB,hC,bound⟩:=F.uniform_whitney_first_holder_bounds (by linarith) small regular i compact inside
    refine ⟨B,C+2*B,hB,by positivity,?_⟩
    intro ε hp hw control
    exact ⟨(bound ε hp hw control).1,LeanShared.BoundedHolderLowering.bound ha.le (by linarith) hB hC
      (bound ε hp hw control).1 (bound ε hp hw control).2⟩
  have high:2≤⌊r⌋₊:=Nat.le_floor (by simpa using le_of_not_gt small)
  have one:1≤⌊r⌋₊:=by omega
  have lowerRegular:=LeanShared.FractionalOneJetLowering.regular_one_add ha ha1 lower regular
  have valid:∀x∈K,x∈(F.atlas.source i).target ∧ T ((F.atlas.source i).symm x)∈(F.atlas.target i).source:=by
    intro x hx
    exact ⟨(inside hx).1,F.atlas.deterministic_target i ⟨_,subset_closure (inside hx).2,rfl⟩⟩
  obtain ⟨B,C,hB,hC,refValue,refHolder⟩:=lowerRegular.compact_one_holder_in_charts ha ha1
    (F.atlas.source i) (F.atlas.target i) (F.atlas.source_smooth i) (F.atlas.target_smooth i) compact valid
  let D:=F.constant*(F.window:ℝ)
  have hD:0≤D:=mul_nonneg F.constant_positive.le F.window.property
  refine ⟨B+D,C+3*D,add_nonneg hB hD,by positivity,?_⟩
  intro ε hp hw control
  let f:=F.atlas.coordinate (F.family ε control.val) i
  let g:=F.atlas.coordinate T i
  have proximity:F.constant*‖control.val‖≤D:=
    (mul_le_mul_of_nonneg_left (LeanShared.NoiseCubeRescaling.cube_norm_le (ε:ℝ) ε.property control)
      F.constant_positive.le).trans (mul_le_mul_of_nonneg_left (show (ε:ℝ)≤(F.window:ℝ) by exact_mod_cast hw)
        F.constant_positive.le)
  have difference:∀x∈K,‖fderiv ℝ f x-fderiv ℝ g x‖≤D:=by
    intro x hx
    have bound:=(F.whitney_bound ε hp hw control).derivatives i 1 one x (inside hx)
    rw [←LeanShared.FirstDerivativeTensorNorm.tensor_fderiv _ x,
      ←LeanShared.FirstDerivativeTensorNorm.tensor_fderiv _ x,←map_sub,LinearIsometryEquiv.norm_map] at bound
    exact bound.trans proximity
  have smoothF:∀x∈K,ContDiffAt ℝ 2 f x:=by
    intro x hx
    apply coordinate_c2 ((F.map_regular ε hp hw control).differentiable.of_le (by exact_mod_cast high))
      _ _ (F.atlas.source_smooth i) (F.atlas.target_smooth i) x (inside hx).1
    exact (F.whitney_bound ε hp hw control).target_control i ⟨_,subset_closure (inside hx).2,rfl⟩
  have smoothG:∀x∈K,ContDiffAt ℝ 2 g x:=fun x hx=>coordinate_c2
    (regular.differentiable.of_le (by exact_mod_cast high)) _ _ (F.atlas.source_smooth i)
      (F.atlas.target_smooth i) x (valid x hx).1 (valid x hx).2
  have lipschitz:∀x∈K,∀y∈K,
      ‖(fderiv ℝ f x-fderiv ℝ g x)-(fderiv ℝ f y-fderiv ℝ g y)‖≤D*‖x-y‖:=by
    intro x hx y hy
    apply LeanShared.SecondDerivativeTensorNorm.derivative_difference_lipschitz convex
      (fun z hz=>((smoothF z hz).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))
      (fun z hz=>((smoothG z hz).fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)) _ hx hy
    intro z hz
    exact ((F.whitney_bound ε hp hw control).derivatives i 2 high z (inside hz)).trans proximity
  have holder:=LeanShared.BoundedHolderLowering.bound ha.le ha1.le hD hD difference
    (fun x hx y hy=>by simpa only [Real.rpow_one] using lipschitz x hx y hy)
  constructor
  · intro x hx
    exact (norm_le_norm_sub_add _ _).trans
      ((add_le_add (difference x hx) (refValue x hx)).trans_eq (by ring))
  · intro x hx y hy
    change ‖fderiv ℝ f x-fderiv ℝ f y‖≤_
    have split:fderiv ℝ f x-fderiv ℝ f y=
      ((fderiv ℝ f x-fderiv ℝ g x)-(fderiv ℝ f y-fderiv ℝ g y))+
        (fderiv ℝ g x-fderiv ℝ g y):=by abel
    rw [split]
    exact (norm_add_le _ _).trans ((add_le_add (holder x hx y hy) (refHolder x hx y hy)).trans_eq (by ring))
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
