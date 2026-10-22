module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The finite-sum shift identity. A single terminal estimate gives a one-step contraction in the
adapted quadratic energy. -/

public section
open scoped BigOperators

namespace LeanShared.FiniteAdaptedEnergy

/-- A hyperbolic exponential bound supplies one positive terminal time for
every strictly weaker target contraction. -/
theorem exists_terminal_time (C q a : ℝ) (positiveC : 0 < C)
    (nonnegativeQ : 0 ≤ q) (positiveA : 0 < a) (slack : q < a) :
    ∃ N : ℕ, 0 < N ∧ C * q ^ N ≤ a ^ N := by
  have ratio_nonnegative : 0 ≤ q / a := div_nonneg nonnegativeQ positiveA.le
  have ratio_small : q / a < 1 := (div_lt_one₀ positiveA).mpr slack
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr positiveC) ratio_small
  have step : (q / a) ^ (n + 1) ≤ (q / a) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg ratio_nonnegative n) ratio_small.le
  have bound : C * (q / a) ^ (n + 1) ≤ 1 := by
    calc
      C * (q / a) ^ (n + 1) ≤ C * C⁻¹ :=
        mul_le_mul_of_nonneg_left (step.trans hn.le) positiveC.le
      _ = 1 := mul_inv_cancel₀ positiveC.ne'
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have quotient : (C * q ^ (n + 1)) / a ^ (n + 1) ≤ 1 := by
    simpa only [div_pow, ← mul_div_assoc] using bound
  exact (div_le_one (pow_pos positiveA _)).mp quotient

@[expose] def energy (weight : ℝ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, weight ^ j * f j

theorem shift_identity (weight : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    weight * energy weight (fun j => f (j + 1)) N =
      energy weight f N - f 0 + weight ^ N * f N := by
  have left := Finset.sum_range_succ (fun j => weight ^ j * f j) N
  have right := Finset.sum_range_succ' (fun j => weight ^ j * f j) N
  have shifted : (∑ j ∈ Finset.range N, weight ^ (j + 1) * f (j + 1)) =
      weight * energy weight (fun j => f (j + 1)) N := by
    simp only [energy, pow_succ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [left, shifted, pow_zero, one_mul] at right
  dsimp only [energy]
  dsimp only [energy] at right
  linarith

theorem contraction (weight : ℝ) (positive : 0 < weight)
    (f : ℕ → ℝ) (N : ℕ) (terminal : weight ^ N * f N ≤ f 0) :
    energy weight (fun j => f (j + 1)) N ≤ (weight⁻¹) * energy weight f N := by
  have bound : weight * energy weight (fun j => f (j + 1)) N ≤ energy weight f N := by
    rw [shift_identity]
    linarith
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using bound)

theorem initial_le (weight : ℝ) (nonnegative : 0 ≤ weight)
    (f : ℕ → ℝ) (positive : ∀ j, 0 ≤ f j) (N : ℕ) (length : 0 < N) :
    f 0 ≤ energy weight f N := by
  have term := Finset.single_le_sum
    (f := fun j => weight ^ j * f j)
    (fun j _ => mul_nonneg (pow_nonneg nonnegative j) (positive j))
    (Finset.mem_range.mpr length)
  simpa only [energy, pow_zero, one_mul] using term

end LeanShared.FiniteAdaptedEnergy
