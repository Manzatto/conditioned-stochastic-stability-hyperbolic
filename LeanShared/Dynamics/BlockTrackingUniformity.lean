module

public import LeanShared.Dynamics.FiniteIterateUniformity
public import Mathlib.Tactic.Linarith

/-! Uniform control at block times gives actual tracking at every
intermediate time, including the final endpoint. -/
public section
namespace LeanShared.BlockTrackingUniformity
variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_tolerance (T : X → X) (continuous : Continuous T) (N : ℕ) (positiveN : 0 < N)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ p : ℕ, ∀ x y : X,
      (∀ j ≤ p, dist (T^[N * j] x) (T^[N * j] y) < η) →
      ∀ k ≤ N * p, dist (T^[k] x) (T^[k] y) < ε := by
  obtain ⟨η, positiveη, intermediate⟩ := FiniteIterateUniformity.exists_tolerance T continuous N ε positiveε
  refine ⟨η, positiveη, fun p x y blocks k hk => ?_⟩
  have quotient : k / N ≤ p := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul positiveN).mpr (by nlinarith))
  have remainder : k % N ≤ N := (Nat.mod_lt k positiveN).le
  have estimate := intermediate (T^[N * (k / N)] x) (T^[N * (k / N)] y)
    (blocks (k / N) quotient) (k % N) remainder
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at estimate
  have size : k % N + N * (k / N) = k := by
    rw [Nat.add_comm]
    exact Nat.div_add_mod k N
  simpa only [size] using estimate

end LeanShared.BlockTrackingUniformity
