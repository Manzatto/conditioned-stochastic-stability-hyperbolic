module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-! Uniform orbit-energy distortion from exponentially matched orbit segments.
The bound is independent of segment length. The geometric matching estimate
is explicit, so this result does not assume a Bowen distortion conclusion. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.HolderBowenDistortion

theorem geometric_sum_bound (r : ℝ) (nonnegative : 0 ≤ r) (small : r < 1)
    (n : ℕ) : (∑ j ∈ Finset.range n, r ^ j) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.mpr small)).mpr
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg nonnegative n)

theorem two_sided_sum_bound (r : ℝ) (nonnegative : 0 ≤ r) (small : r < 1)
    (n : ℕ) : (∑ j ∈ Finset.range n, r ^ min j (n - 1 - j)) ≤ 2 / (1 - r) := by
  have pointwise (j : ℕ) : r ^ min j (n - 1 - j) ≤ r ^ j + r ^ (n - 1 - j) := by
    rcases le_total j (n - 1 - j) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg nonnegative _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg nonnegative _)
  calc
    _ ≤ ∑ j ∈ Finset.range n, (r ^ j + r ^ (n - 1 - j)) :=
      Finset.sum_le_sum (fun j _ => pointwise j)
    _ = 2 * ∑ j ∈ Finset.range n, r ^ j := by
      rw [Finset.sum_add_distrib, Finset.sum_range_reflect]
      ring
    _ ≤ 2 * (1 / (1 - r)) := mul_le_mul_of_nonneg_left
      (geometric_sum_bound r nonnegative small n) (by norm_num)
    _ = _ := by ring

variable {X : Type*} [PseudoMetricSpace X]

/-- Hölder energy distortion along a pair of exponentially matched segments. -/
theorem energy_bound (ψ : X → ℝ) (H C α θ : ℝ)
    (Hnonnegative : 0 ≤ H) (Cnonnegative : 0 ≤ C)
    (αpositive : 0 < α) (θnonnegative : 0 ≤ θ) (θsmall : θ < 1)
    (holder : ∀ x y, |ψ x - ψ y| ≤ H * dist x y ^ α)
    (n : ℕ) (x y : ℕ → X)
    (matching : ∀ j < n, dist (x j) (y j) ≤ C * θ ^ min j (n - 1 - j)) :
    |(∑ j ∈ Finset.range n, ψ (x j)) - (∑ j ∈ Finset.range n, ψ (y j))| ≤
      2 * H * C ^ α / (1 - θ ^ α) := by
  have powered (m : ℕ) : (θ ^ m) ^ α = (θ ^ α) ^ m := by
    rw [← Real.rpow_natCast_mul θnonnegative, mul_comm, Real.rpow_mul θnonnegative,
      Real.rpow_natCast]
  have small : θ ^ α < 1 := Real.rpow_lt_one θnonnegative θsmall αpositive
  have estimate (j : ℕ) (hj : j < n) :
      |ψ (x j) - ψ (y j)| ≤ (H * C ^ α) * (θ ^ α) ^ min j (n - 1 - j) := by
    calc
      _ ≤ H * dist (x j) (y j) ^ α := holder _ _
      _ ≤ H * (C * θ ^ min j (n - 1 - j)) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow dist_nonneg (matching j hj) αpositive.le) Hnonnegative
      _ = _ := by rw [Real.mul_rpow Cnonnegative (pow_nonneg θnonnegative _), powered]; ring
  calc
    _ = |∑ j ∈ Finset.range n, (ψ (x j) - ψ (y j))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range n, |ψ (x j) - ψ (y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, (H * C ^ α) * (θ ^ α) ^ min j (n - 1 - j) :=
      Finset.sum_le_sum (fun j hj => estimate j (Finset.mem_range.mp hj))
    _ = (H * C ^ α) * ∑ j ∈ Finset.range n, (θ ^ α) ^ min j (n - 1 - j) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (H * C ^ α) * (2 / (1 - θ ^ α)) :=
      mul_le_mul_of_nonneg_left
        (two_sided_sum_bound _ (Real.rpow_nonneg θnonnegative α) small n)
        (mul_nonneg Hnonnegative (Real.rpow_nonneg Cnonnegative α))
    _ = _ := by ring

end LeanShared.HolderBowenDistortion
