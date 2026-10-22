module
public import LeanShared.Analysis.LowOrderChartPairing

/-! The dyadic series of the multiplier estimate: for exponents `e, q` with `e - 1 - q < 0`, `-1 - q
< 0` and `e ≤ 1`, the sums `∑_l 2^{e n - max(n,l) - q l}` are bounded uniformly in `n`, by
splitting at `l = n` and comparing with two geometric series. -/
public noncomputable section
open Finset
namespace LeanShared.ConeMultiplierSeries

/-- The uniform bound. -/
def bound (e q : ℝ) : ℝ :=
  (1 - (2 : ℝ) ^ (e - 1 - q))⁻¹ + (1 - (2 : ℝ) ^ (max e 0 - 1 - q))⁻¹

theorem ratio_lt_one {x : ℝ} (hx : x < 0) : (2 : ℝ) ^ x < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hx

theorem term_le (e q : ℝ) (h3 : e ≤ 1) (n l : ℕ) :
    (2 : ℝ) ^ (e * n - (max n l : ℕ) - q * l) ≤
      ((2 : ℝ) ^ (e - 1 - q)) ^ l + ((2 : ℝ) ^ (max e 0 - 1 - q)) ^ l := by
  have two : (1 : ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (e - 1 - q)) l, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast ((2 : ℝ) ^ (max e 0 - 1 - q)) l, ← Real.rpow_mul (by norm_num)]
  rcases le_total l n with hl | hl
  · have hmax : ((max n l : ℕ) : ℝ) = n := by rw [max_eq_left hl]
    rw [hmax]
    have hle : e * n - n - q * l ≤ (e - 1 - q) * l := by
      have : (e - 1) * ((n : ℝ) - l) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr (by exact_mod_cast hl))
      nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le two hle).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _))
  · have hmax : ((max n l : ℕ) : ℝ) = l := by rw [max_eq_right hl]
    rw [hmax]
    have hle : e * n - l - q * l ≤ (max e 0 - 1 - q) * l := by
      have h1 : e * n ≤ max e 0 * n :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      have h2 : max e 0 * n ≤ max e 0 * l :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hl) (le_max_right _ _)
      nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le two hle).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _))

theorem sum_le (e q : ℝ) (h1 : e - 1 - q < 0) (h2 : -1 - q < 0) (h3 : e ≤ 1) (n N : ℕ) :
    ∑ l ∈ range (N + 1), (2 : ℝ) ^ (e * n - (max n l : ℕ) - q * l) ≤ bound e q := by
  have hmax : max e 0 - 1 - q < 0 := by
    rcases le_total e 0 with he | he
    · rw [max_eq_right he]; linarith
    · rw [max_eq_left he]; exact h1
  calc ∑ l ∈ range (N + 1), (2 : ℝ) ^ (e * n - (max n l : ℕ) - q * l)
      ≤ ∑ l ∈ range (N + 1), (((2 : ℝ) ^ (e - 1 - q)) ^ l + ((2 : ℝ) ^ (max e 0 - 1 - q)) ^ l) :=
        sum_le_sum fun l _ => term_le e q h3 n l
    _ = ∑ l ∈ range (N + 1), ((2 : ℝ) ^ (e - 1 - q)) ^ l +
          ∑ l ∈ range (N + 1), ((2 : ℝ) ^ (max e 0 - 1 - q)) ^ l := sum_add_distrib
    _ ≤ bound e q :=
        add_le_add
          (LowOrderChartPairing.geometric_bound (Real.rpow_nonneg (by norm_num) _)
            (ratio_lt_one h1) N)
          (LowOrderChartPairing.geometric_bound (Real.rpow_nonneg (by norm_num) _)
            (ratio_lt_one hmax) N)

theorem bound_nonneg (e q : ℝ) (h1 : e - 1 - q < 0) (h2 : -1 - q < 0) : 0 ≤ bound e q := by
  have hmax : max e 0 - 1 - q < 0 := by
    rcases le_total e 0 with he | he
    · rw [max_eq_right he]; linarith
    · rw [max_eq_left he]; exact h1
  exact add_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (ratio_lt_one h1).le))
    (inv_nonneg.mpr (sub_nonneg.mpr (ratio_lt_one hmax).le))

end LeanShared.ConeMultiplierSeries
