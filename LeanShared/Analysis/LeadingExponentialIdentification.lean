module

public import LeanShared.Analysis.ExponentialSequenceLogLimit
public import Mathlib.Analysis.SpecificLimits.Normed

/-! A genuine leading exponential of a coding coefficient sequence is
identified with the original pressure when the literal coefficient error
grows strictly slower than that pressure.  No pressure equality for the
symbolic extension is assumed.  Indices denote positive period n+1.
-/

public section
namespace LeanShared.LeadingExponentialIdentification
open Filter
open scoped Topology

theorem eq_exp (a b : ℕ → ℝ) (P ρ κ Cₐ β Cᵦ : ℝ)
    (positiveρ : 0 < ρ) (positiveκ : 0 < κ) (smallκ : κ < 1) (nonnegativeA : 0 ≤ Cₐ)
    (positiveβ : 0 < β) (smallβ : β < Real.exp P) (nonnegativeB : 0 ≤ Cᵦ)
    (normalized : ∀ n, |(ρ ^ (n + 1))⁻¹ * a n - 1| ≤ Cₐ * κ ^ (n + 1))
    (comparison : ∀ n, |a n - b n| ≤ Cᵦ * β ^ (n + 1))
    (positiveB : ∀ᶠ n in atTop, 0 < b n)
    (growth : Tendsto (fun n => Real.log (b n) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 P)) :
    ρ = Real.exp P := by
  by_cases above : Real.exp P ≤ ρ
  · have βless : β < ρ := smallβ.trans_le above
    have positiveRatio : 0 < β / ρ := div_pos positiveβ positiveρ
    have smallRatio : β / ρ < 1 := (div_lt_one positiveρ).mpr βless
    have error (n : ℕ) : |(ρ ^ (n + 1))⁻¹ * (b n - a n)| ≤ Cᵦ * (β / ρ) ^ (n + 1) := by
      have given := comparison n
      rw [abs_sub_comm] at given
      rw [abs_mul, abs_of_pos (inv_pos.mpr (pow_pos positiveρ _))]
      calc
        _ ≤ (ρ ^ (n + 1))⁻¹ * (Cᵦ * β ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left given (by positivity)
        _ = _ := by rw [div_pow]; ring
    have total (n : ℕ) : |(ρ ^ (n + 1))⁻¹ * b n - 1| ≤
        Cₐ * κ ^ (n + 1) + Cᵦ * (β / ρ) ^ (n + 1) := by
      have identity : (ρ ^ (n + 1))⁻¹ * b n - 1 =
          ((ρ ^ (n + 1))⁻¹ * a n - 1) + (ρ ^ (n + 1))⁻¹ * (b n - a n) := by ring
      rw [identity]
      exact (abs_add_le _ _).trans (add_le_add (normalized n) (error n))
    have geometric (r : ℝ) (nonnegative : 0 ≤ r) (small : r < 1) :
        Tendsto (fun n : ℕ => r ^ (n + 1)) atTop (𝓝 0) := by
      simpa only [pow_succ, zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one nonnegative small).mul_const r
    have decays : Tendsto (fun n => Cₐ * κ ^ (n + 1) + Cᵦ * (β / ρ) ^ (n + 1)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using
        ((geometric κ positiveκ.le smallκ).const_mul Cₐ).add
          ((geometric (β / ρ) positiveRatio.le smallRatio).const_mul Cᵦ)
    have absolute := squeeze_zero (fun n => abs_nonneg ((ρ ^ (n + 1))⁻¹ * b n - 1)) total decays
    have ratio : Tendsto (fun n => (ρ ^ (n + 1))⁻¹ * b n) atTop (𝓝 1) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using absolute
    have same : P = Real.log ρ := tendsto_nhds_unique growth
      (ExponentialSequenceLogLimit.of_ratio b ρ positiveρ ratio)
    rw [same, Real.exp_log positiveρ]
  · let γ := max ρ β
    have positiveγ : 0 < γ := positiveρ.trans_le (le_max_left _ _)
    have smallγ : γ < Real.exp P := max_lt (lt_of_not_ge above) smallβ
    have upperA (n : ℕ) : a n ≤ (1 + Cₐ) * ρ ^ (n + 1) := by
      have smallPower : κ ^ (n + 1) ≤ 1 := pow_le_one₀ positiveκ.le smallκ.le
      have relative := (normalized n).trans (mul_le_of_le_one_right nonnegativeA smallPower)
      have upper := (le_abs_self ((ρ ^ (n + 1))⁻¹ * a n - 1)).trans relative
      have identity : a n = ρ ^ (n + 1) * ((ρ ^ (n + 1))⁻¹ * a n) := by field_simp
      calc
        _ = _ := identity
        _ ≤ ρ ^ (n + 1) * (1 + Cₐ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring
    have upperB (n : ℕ) : b n ≤ (1 + Cₐ + Cᵦ) * γ ^ (n + 1) := by
      have difference := comparison n
      have reverse := le_abs_self (b n - a n)
      rw [abs_sub_comm] at difference
      have first : b n ≤ a n + Cᵦ * β ^ (n + 1) := by linarith
      calc
        _ ≤ (1 + Cₐ) * ρ ^ (n + 1) + Cᵦ * β ^ (n + 1) := first.trans (add_le_add (upperA n) le_rfl)
        _ ≤ (1 + Cₐ) * γ ^ (n + 1) + Cᵦ * γ ^ (n + 1) := add_le_add
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positiveρ.le (le_max_left _ _) _) (by positivity))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positiveβ.le (le_max_right _ _) _) nonnegativeB)
        _ = _ := by ring
    have rate := ExponentialSequenceLogLimit.le_of_upper b P (1 + Cₐ + Cᵦ) γ
      (by positivity) positiveγ positiveB growth upperB
    have exponent := Real.exp_le_exp.mpr rate
    rw [Real.exp_log positiveγ] at exponent
    exact (not_le_of_gt smallγ exponent).elim

end LeanShared.LeadingExponentialIdentification
