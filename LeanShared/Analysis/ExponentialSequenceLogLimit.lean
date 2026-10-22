module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual relative exponential asymptotics determine normalized
logarithmic growth, and a geometric upper bound bounds that growth.
The sequence index denotes positive period n+1 throughout.
-/

public section
namespace LeanShared.ExponentialSequenceLogLimit
open Filter
open scoped Topology

theorem of_ratio (f : ℕ → ℝ) (ρ : ℝ) (positiveρ : 0 < ρ)
    (ratio : Tendsto (fun n => (ρ ^ (n + 1))⁻¹ * f n) atTop (𝓝 1)) :
    Tendsto (fun n => Real.log (f n) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.log ρ)) := by
  let r := fun n => (ρ ^ (n + 1))⁻¹ * f n
  have positiveR : ∀ᶠ n in atTop, 0 < r n := ratio.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have logRatio : Tendsto (fun n => Real.log (r n)) atTop (𝓝 0) := by
    simpa only [Real.log_one] using ratio.log (by norm_num : (1 : ℝ) ≠ 0)
  have inverse : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have limit : Tendsto (fun n => Real.log ρ + Real.log (r n) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.log ρ)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using tendsto_const_nhds.add (logRatio.mul inverse)
  apply limit.congr'
  filter_upwards [positiveR] with n positive
  have identity : f n = ρ ^ (n + 1) * r n := by
    dsimp [r]
    field_simp
  have nonzeroN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  symm
  calc
    _ = Real.log (ρ ^ (n + 1) * r n) / ((n + 1 : ℕ) : ℝ) := congrArg (fun x => Real.log x / ((n + 1 : ℕ) : ℝ)) identity
    _ = _ := by
      rw [Real.log_mul (ne_of_gt (pow_pos positiveρ _)) positive.ne', Real.log_pow]
      field_simp

theorem le_of_upper (f : ℕ → ℝ) (P C γ : ℝ) (positiveC : 0 < C) (positiveγ : 0 < γ)
    (positive : ∀ᶠ n in atTop, 0 < f n)
    (limit : Tendsto (fun n => Real.log (f n) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 P))
    (upper : ∀ n, f n ≤ C * γ ^ (n + 1)) : P ≤ Real.log γ := by
  have inverse : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have upperLimit : Tendsto (fun n => Real.log γ + Real.log C / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (Real.log γ)) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add (inverse.const_mul (Real.log C))
  apply le_of_tendsto_of_tendsto limit upperLimit
  filter_upwards [positive] with n hn
  have logs := Real.log_le_log hn (upper n)
  rw [Real.log_mul positiveC.ne' (ne_of_gt (pow_pos positiveγ _)), Real.log_pow] at logs
  have realN : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have bound := div_le_div_of_nonneg_right logs realN.le
  have algebra : (Real.log C + ((n + 1 : ℕ) : ℝ) * Real.log γ) / ((n + 1 : ℕ) : ℝ) =
      Real.log γ + Real.log C / ((n + 1 : ℕ) : ℝ) := by
    field_simp
    ring
  exact bound.trans_eq algebra

end LeanShared.ExponentialSequenceLogLimit
