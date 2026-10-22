module

public import LeanShared.Dynamics.HolderBowenDistortion

/-! Summation of nonautonomous geometric distortion estimates. The local
observable can vary with the selected chart and time. -/
public section
open scoped BigOperators
namespace LeanShared.HolderBowenDistortion

theorem sum_difference_bound (a b : ℕ → ℝ) (A r : ℝ)
    (Anonnegative : 0 ≤ A) (rnonnegative : 0 ≤ r) (rsmall : r < 1)
    (n : ℕ) (bound : ∀ j < n,
      |a j - b j| ≤ A * r ^ min j (n - 1 - j)) :
    |(∑ j ∈ Finset.range n, a j) - (∑ j ∈ Finset.range n, b j)| ≤
      2 * A / (1 - r) := by
  calc
    _ = |∑ j ∈ Finset.range n, (a j - b j)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range n, |a j - b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, A * r ^ min j (n - 1 - j) :=
      Finset.sum_le_sum (fun j hj => bound j (Finset.mem_range.mp hj))
    _ = A * ∑ j ∈ Finset.range n, r ^ min j (n - 1 - j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ A * (2 / (1 - r)) := mul_le_mul_of_nonneg_left
      (two_sided_sum_bound r rnonnegative rsmall n) Anonnegative
    _ = _ := by ring

end LeanShared.HolderBowenDistortion
