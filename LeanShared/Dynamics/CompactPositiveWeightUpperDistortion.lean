module

public import LeanShared.Topology.CompactNearDiagonalContinuity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Uniform upper weight distortion near a compact positive core, with
arbitrarily small exponential loss, also for points outside the core. -/
public noncomputable section
namespace LeanShared.CompactPositiveWeightUpperDistortion
open Set
variable {X : Type*} [PseudoMetricSpace X]

theorem exists_radius (K : Set X) (compact : IsCompact K) (g : X → ℝ)
    (continuous : Continuous g) (positive : ∀ x ∈ K, 0 < g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y, dist x y < ρ →
      0 < g y ∧ g y ≤ Real.exp ε * g x := by
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
  have upper : Real.log (g y) < ε + Real.log (g x) := by
    linarith [(abs_lt.mp difference).1]
  refine ⟨hy, ?_⟩
  have exponent := (Real.exp_lt_exp.mpr upper).le
  rw [Real.exp_add, Real.exp_log (positive x hx), Real.exp_log hy] at exponent
  exact exponent

/-- One spatial radius controls products at every finite length. -/
theorem exists_orbit_radius (K : Set X) (compact : IsCompact K) (g : X → ℝ)
    (continuous : Continuous g) (positive : ∀ x ∈ K, 0 < g x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ, ∀ x y : ℕ → X,
      (∀ i < n, x i ∈ K) → (∀ i < n, dist (x i) (y i) < ρ) →
      0 < (∏ i ∈ Finset.range n, g (y i)) ∧
      (∏ i ∈ Finset.range n, g (y i)) ≤
        Real.exp (ε * n) * (∏ i ∈ Finset.range n, g (x i)) := by
  obtain ⟨ρ, hρ, nearby⟩ := exists_radius K compact g continuous positive ε hε
  refine ⟨ρ, hρ, fun n x y core close => ?_⟩
  have point (i : ℕ) (hi : i ∈ Finset.range n) :=
    nearby (x i) (core i (Finset.mem_range.mp hi)) (y i) (close i (Finset.mem_range.mp hi))
  refine ⟨Finset.prod_pos (fun i hi => (point i hi).1), ?_⟩
  have product := Finset.prod_le_prod₀ (fun i hi => (point i hi).1.le)
    (fun i hi => (point i hi).2)
  have identity : (∏ i ∈ Finset.range n, (Real.exp ε * g (x i))) =
      Real.exp (ε * n) * (∏ i ∈ Finset.range n, g (x i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [identity] at product
  exact product

end LeanShared.CompactPositiveWeightUpperDistortion
