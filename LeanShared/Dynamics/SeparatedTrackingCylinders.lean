module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Tactic.Linarith

/-! Actual cylinders tracking a separated family with radius ε/3 are
disjoint. Thus their positive matrix coefficients can be summed. -/
public section
namespace LeanShared.SeparatedTrackingCylinders
open Set
variable {X : Type*} [MetricSpace X]

theorem pairwise_disjoint (T : X → X) (K : Set X) (n : ℕ) (ε : ℝ) (positiveε : 0 < ε)
    (s : Finset X) (separated : ThermodynamicDefinitions.Separated T K n ε s)
    (W : X → Set X)
    (tracking : ∀ x ∈ s, ∀ z ∈ W x, ∀ j < n, dist (T^[j] z) (T^[j] x) < ε / 3) :
    (s : Set X).Pairwise (fun x y => Disjoint (W x) (W y)) := by
  intro x hx y hy different
  rw [Set.disjoint_left]
  intro z hzx hzy
  obtain ⟨j, before, apart⟩ := separated.2 x hx y hy different
  have left := tracking x hx z hzx j before
  have right := tracking y hy z hzy j before
  have triangle := dist_triangle (T^[j] x) (T^[j] z) (T^[j] y)
  rw [dist_comm (T^[j] x) (T^[j] z)] at triangle
  linarith

end LeanShared.SeparatedTrackingCylinders
