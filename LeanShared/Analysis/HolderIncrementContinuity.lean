module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic

/-! Quantitative positive Holder increments imply continuity without
requiring separability or a topology on any external family index. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.HolderIncrementContinuity
variable {X F:Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]

theorem continuous {f:X→F} {C a:ℝ} (ha:0<a)
    (holder:∀x y,‖f x-f y‖≤C*dist x y^a):Continuous f:=by
  rw [continuous_iff_continuousAt]
  intro x
  have major:Continuous (fun y:X=>C*dist y x^a):=
    continuous_const.mul ((continuous_id.dist continuous_const).rpow_const (fun _=>Or.inr ha.le))
  have tends:Tendsto (fun y:X=>C*dist y x^a) (𝓝 x) (𝓝 0):=by
    simpa only [dist_self,Real.zero_rpow ha.ne',mul_zero] using major.tendsto x
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _=>dist_nonneg) (fun y=>?_) tends
  simpa only [dist_eq_norm] using holder y x
end LeanShared.HolderIncrementContinuity
