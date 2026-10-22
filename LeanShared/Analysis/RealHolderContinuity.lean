module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Basic

/-! A literal real two-point Hölder estimate gives continuity on the
actual subset. No extended-distance reformulation is a premise. -/
public section
namespace LeanShared.RealHolderContinuity
open Set Filter Metric
open scoped Topology
variable {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]

theorem continuousOn (S : Set X) (f : X → Y) (α C : ℝ) (positive : 0 < α)
    (bound : ∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ C * dist x y ^ α) : ContinuousOn f S := by
  intro x hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε positiveε
  have limit : Tendsto (fun t : ℝ => C * t ^ α) (nhds 0) (nhds 0) := by
    have continuous : ContinuousAt (fun t : ℝ => C * t ^ α) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr positive.le))
    simpa only [Real.zero_rpow positive.ne', mul_zero] using continuous.tendsto
  have small : ∀ᶠ t : ℝ in nhds 0, C * t ^ α < ε := limit.eventually (gt_mem_nhds positiveε)
  obtain ⟨δ, positiveδ, safe⟩ := Metric.mem_nhds_iff.mp small
  refine ⟨δ, positiveδ, fun y hy near => ?_⟩
  have power := safe (show dist y x ∈ ball (0 : ℝ) δ from by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using near)
  rw [dist_eq_norm]
  exact (bound y hy x hx).trans_lt power

end LeanShared.RealHolderContinuity
