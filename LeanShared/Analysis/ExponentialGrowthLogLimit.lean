module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! A fixed-shift exponential lower estimate and arbitrarily sharp
exponential upper estimates force the actual normalized logarithmic limit. -/
public section
namespace LeanShared.ExponentialGrowthLogLimit
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem tendsto (f : ℕ → ℝ) (P C : ℝ) (positiveC : 0 < C)
    (gap : ℕ) (lower : ∀ n : ℕ, C * Real.exp (((n + 1 : ℕ) : ℝ) * P) ≤ f (n + gap))
    (upper : ∀ η > 0, ∀ᶠ n : ℕ in atTop,
      f (n + 1) ≤ Real.exp (((n + 1 : ℕ) : ℝ) * (P + η))) :
    Tendsto (fun n : ℕ => Real.log (f n) / (n : ℝ)) atTop (𝓝 P) := by
  have lowerEventually : ∀ᶠ n : ℕ in atTop,
      0 < f n ∧ Real.log C + ((n : ℝ) + 1 - gap) * P ≤ Real.log (f n) := by
    filter_upwards [eventually_ge_atTop gap] with n hn
    have estimate := lower (n - gap)
    rw [Nat.sub_add_cancel hn] at estimate
    have positive : 0 < f n := (mul_pos positiveC (Real.exp_pos _)).trans_le estimate
    refine ⟨positive, ?_⟩
    have logs := Real.log_le_log (mul_pos positiveC (Real.exp_pos _)) estimate
    rw [Real.log_mul positiveC.ne' (Real.exp_pos _).ne', Real.log_exp] at logs
    have index : (((n - gap + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 - gap := by
      rw [Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
      ring
    rwa [index] at logs
  have affineLimit : Tendsto (fun n : ℕ =>
      P + (Real.log C + (1 - (gap : ℝ)) * P) * (n : ℝ)⁻¹) atTop (𝓝 P) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      (tendsto_inv_atTop_nhds_zero_nat.const_mul (Real.log C + (1 - (gap : ℝ)) * P))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [lowerEventually, eventually_gt_atTop 0,
      affineLimit.eventually (lt_mem_nhds ha)] with n hn positiveN affine
    have realN : (0 : ℝ) < n := by exact_mod_cast positiveN
    have bound := (div_le_div_of_nonneg_right hn.2 realN.le)
    have identity : (Real.log C + ((n : ℝ) + 1 - gap) * P) / n =
        P + (Real.log C + (1 - (gap : ℝ)) * P) * (n : ℝ)⁻¹ := by
      field_simp [realN.ne']
      ring
    rw [identity] at bound
    exact affine.trans_le bound
  · intro b hb
    let η := (b - P) / 2
    have positiveη : 0 < η := by dsimp [η]; linarith
    obtain ⟨N, eventualUpper⟩ := eventually_atTop.mp (upper η positiveη)
    filter_upwards [lowerEventually, eventually_ge_atTop (N + 1)] with n hn hnN
    have positiveN : 0 < n := by omega
    have realN : (0 : ℝ) < n := by exact_mod_cast positiveN
    have estimate := eventualUpper (n - 1) (by omega)
    have index : n - 1 + 1 = n := by omega
    rw [index] at estimate
    have logs := Real.log_le_log hn.1 estimate
    rw [Real.log_exp] at logs
    have result : Real.log (f n) / n ≤ P + η := (div_le_iff₀ realN).mpr (by nlinarith [logs])
    exact result.trans_lt (by dsimp [η]; linarith)

end LeanShared.ExponentialGrowthLogLimit
