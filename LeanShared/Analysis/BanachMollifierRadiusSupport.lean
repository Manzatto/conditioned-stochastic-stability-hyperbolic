module
public import LeanShared.Analysis.BanachNormalizedKernelDilation
public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

/-! Uniform physical support with a selectable mollifier radius.
The radius can fit an actual chart diffeomorphism neighborhood. -/
public noncomputable section
open Set MeasureTheory
open scoped Convolution BoundedContinuousFunction Pointwise
namespace LeanShared.BanachMollifierRadiusSupport
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem support_subset (μ:Measure E) [μ.IsAddHaarMeasure]
    {κ:E→ℝ} (ρ:ℝ) (small:Function.support κ⊆Metric.closedBall 0 ρ)
    (q:E→ᵇF) {K:Set E} (compact:IsCompact K)
    (supported:tsupport (fun x=>q x)⊆K) {r:ℝ} (hr:1≤r):
    tsupport (BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ]
      (fun x=>q x))⊆K+Metric.closedBall 0 ρ:=by
  have closed:IsClosed (K+Metric.closedBall (0:E) ρ):=
    (compact.add (isCompact_closedBall (0:E) ρ)).isClosed
  apply closure_minimal _ closed
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩:=support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hx
  refine ⟨a,supported (subset_closure ha),b,?_,rfl⟩
  have nonzero:κ (r • b)≠0:=by
    intro hz
    exact hb (by simp [BanachNormalizedKernelDilation.dilate,hz])
  have nb:‖r • b‖≤ρ:=by simpa only [Metric.mem_closedBall,dist_zero_right] using small nonzero
  have positive:0<r:=zero_lt_one.trans_le hr
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos positive] at nb
  have le:‖b‖≤ρ:=by nlinarith [norm_nonneg b]
  simpa only [Metric.mem_closedBall,dist_zero_right] using le
end LeanShared.BanachMollifierRadiusSupport
