module

public import LeanShared.Topology.CompactNearDiagonalContinuity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith

/-! Actual continuous weights positive on a compact core have arbitrarily
small exponential loss on nearby finite orbit segments, including segments
outside the core. No off-core global positivity or Hölder premise is used. -/
public noncomputable section
namespace LeanShared.CompactPositiveWeightDistortion
open Set
variable {X : Type*} [PseudoMetricSpace X]

theorem exists_radius (K : Set X) (compact : IsCompact K) (g : X → ℝ)
    (continuous : Continuous g) (positive : ∀ x ∈ K, 0 < g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y, dist x y < ρ →
      0 < g y ∧ Real.exp (-ε) * g x ≤ g y := by
  let U := {x | 0 < g x}
  have openU : IsOpen U := isOpen_lt continuous_const continuous
  have logs : ContinuousOn (fun x => Real.log (g x)) U :=
    continuous.continuousOn.log (fun x hx => ne_of_gt hx)
  obtain ⟨ρ, hρ, close⟩ := CompactNearDiagonalContinuity.exists_radius K U compact openU positive
    (fun x => Real.log (g x)) logs ε hε
  refine ⟨ρ, hρ, fun x hx y hxy => ?_⟩
  obtain ⟨hy, bound⟩ := close x hx y hxy
  have difference : |Real.log (g x) - Real.log (g y)| < ε := by
    simpa only [Real.dist_eq] using bound
  have lower : -ε + Real.log (g x) < Real.log (g y) := by
    linarith [(abs_lt.mp difference).2]
  refine ⟨hy, ?_⟩
  have exponent := (Real.exp_lt_exp.mpr lower).le
  rw [Real.exp_add, Real.exp_log (positive x hx), Real.exp_log hy] at exponent
  exact exponent

end LeanShared.CompactPositiveWeightDistortion
