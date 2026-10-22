module
public import LeanShared.Analysis.ExponentialPrincipalFactor

/-! The literal radial constants of the actual adapted word estimates give
one strict geometric principal decay rate before the horizon is chosen. -/
public noncomputable section
namespace LeanShared.AdaptedWordPrincipalDecay

theorem exists_decay {μ ν t s : ℝ} (positiveμ : 0 < μ) (smallμ : μ < 1)
    (largeν : 1 < ν) (positiveT : 0 < t) (negativeS : s < 0) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ γ < 1 ∧ ∀ N : ℕ,
      max ((10 * μ^N)^t) (((4 * (ν⁻¹)^N)⁻¹)^s) ≤ C * γ^N := by
  let q := max μ ν⁻¹
  have positiveν : 0 < ν := lt_trans zero_lt_one largeν
  have positiveInverse : 0 < ν⁻¹ := inv_pos.mpr positiveν
  have smallInverse : ν⁻¹ < 1 := (inv_lt_one₀ positiveν).mpr largeν
  have positiveq : 0 < q := positiveμ.trans_le (le_max_left _ _)
  have smallq : q < 1 := max_lt smallμ smallInverse
  let C := max ((10 : ℝ)^t) ((10 : ℝ)^(-s))
  let γ := max (q^t) (q^(-s))
  have positiveC : 0 < C := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<10) t).trans_le (le_max_left _ _)
  have rate := ExponentialPrincipalFactor.rate_positive_lt_one positiveq smallq positiveT (neg_pos.mpr negativeS)
  refine ⟨C,γ,positiveC,rate.1,rate.2,?_⟩
  intro N
  have stableBound : 10*μ^N ≤ 10*q^N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positiveμ.le (le_max_left _ _) N) (by norm_num)
  have inverseBound : 4*(ν⁻¹)^N ≤ 10*q^N :=
    mul_le_mul (by norm_num : (4:ℝ)≤10)
      (pow_le_pow_left₀ positiveInverse.le (le_max_right _ _) N)
      (pow_nonneg positiveInverse.le N) (by norm_num)
  have bound := ExponentialPrincipalFactor.bound 10 q t (-s) (10*μ^N) (4*(ν⁻¹)^N) N
    (by norm_num) positiveq.le positiveT.le (neg_nonneg.mpr negativeS.le)
    (mul_nonneg (by norm_num) (pow_nonneg positiveμ.le N))
    (mul_nonneg (by norm_num) (pow_nonneg positiveInverse.le N)) stableBound inverseBound
  rw [← Real.rpow_neg_eq_inv_rpow]
  exact bound

end LeanShared.AdaptedWordPrincipalDecay
