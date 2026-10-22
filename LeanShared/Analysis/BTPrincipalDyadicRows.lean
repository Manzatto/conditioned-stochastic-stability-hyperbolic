module
public import LeanShared.Analysis.BTLinkedDyadicRows

/-! Uniform principal linked-row factor, with the literal BT log thresholds. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.BTLinkedDyadicWeights
theorem principal_row_bound (t s upper lower : ℝ) (ht : 0 < t) (hs : s < 0)
    (upperPositive : 0 < upper) (lowerPositive : 0 < lower) (output : ℕ × Bool) (J : Finset ℕ) :
    (∑ l ∈ J.filter (fun l => linked (plusThreshold upper) (minusThreshold lower) output (l,true)),
      (2 : ℝ)^(exponent t s output.2*output.1-t*l)) +
    (∑ l ∈ J.filter (fun l => linked (plusThreshold upper) (minusThreshold lower) output (l,false)),
      (2 : ℝ)^(exponent t s output.2*output.1-s*l)) ≤
      (max ((2 : ℝ)^(6*t)) ((2 : ℝ)^(-7*s)) * rowConstant t s) * max (upper^t) (lower^s) := by
  have threshold : max ((2 : ℝ)^(t*plusThreshold upper)) ((2 : ℝ)^(s*minusThreshold lower)) ≤
      max ((2 : ℝ)^(6*t)) ((2 : ℝ)^(-7*s)) * max (upper^t) (lower^s) := by
    apply max_le
    · apply (plus_threshold_bound upper t upperPositive ht.le).trans
      exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
        (Real.rpow_nonneg upperPositive.le _) (le_max_of_le_left (Real.rpow_nonneg (by norm_num) _))
    · apply (minus_threshold_bound lower s lowerPositive hs.le).trans
      exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (Real.rpow_nonneg lowerPositive.le _) (le_max_of_le_left (Real.rpow_nonneg (by norm_num) _))
  exact (row_bound t s ht hs (plusThreshold upper) (minusThreshold lower) output J).trans
    ((mul_le_mul_of_nonneg_right threshold (rowConstant_positive t s ht hs).le).trans_eq (by ring))
end LeanShared.BTLinkedDyadicWeights
