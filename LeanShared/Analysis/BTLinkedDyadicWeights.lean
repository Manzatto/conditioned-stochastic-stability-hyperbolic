module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith

/-! The literal Baladi--Tsujii linked relation (input sign first in its
three clauses) gives a uniform weighted dyadic coefficient, including the
mixed positive-input/negative-output branch. -/
public noncomputable section
namespace LeanShared.BTLinkedDyadicWeights

@[expose] def exponent (t s : ℝ) : Bool → ℝ
  | true => t
  | false => s

@[expose] def linked (hplus hminus : ℤ) (output input : ℕ × Bool) : Prop :=
  (input.2 = true ∧ output.2 = true ∧ (output.1 : ℤ) ≤ (input.1 : ℤ) + hplus) ∨
  (input.2 = false ∧ output.2 = false ∧ (input.1 : ℤ) + hminus ≤ (output.1 : ℤ)) ∨
  (input.2 = true ∧ output.2 = false ∧
    (hminus ≤ (output.1 : ℤ) ∨ -hplus ≤ (input.1 : ℤ)))

theorem weight_bound (t s : ℝ) (ht : 0 ≤ t) (hs : s ≤ 0)
    (hplus hminus : ℤ) (output input : ℕ × Bool) (relation : linked hplus hminus output input) :
    (2 : ℝ) ^ (exponent t s output.2 * output.1 - exponent t s input.2 * input.1) ≤
      max ((2 : ℝ) ^ (t * hplus)) ((2 : ℝ) ^ (s * hminus)) := by
  have plus (bound : exponent t s output.2 * output.1 - exponent t s input.2 * input.1 ≤ t * hplus) :
      (2 : ℝ) ^ (exponent t s output.2 * output.1 - exponent t s input.2 * input.1) ≤
        max ((2 : ℝ) ^ (t * hplus)) ((2 : ℝ) ^ (s * hminus)) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) bound).trans (le_max_left _ _)
  have minus (bound : exponent t s output.2 * output.1 - exponent t s input.2 * input.1 ≤ s * hminus) :
      (2 : ℝ) ^ (exponent t s output.2 * output.1 - exponent t s input.2 * input.1) ≤
        max ((2 : ℝ) ^ (t * hplus)) ((2 : ℝ) ^ (s * hminus)) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) bound).trans (le_max_right _ _)
  rcases relation with ⟨hi, ho, level⟩ | ⟨hi, ho, level⟩ | ⟨hi, ho, level⟩
  · apply plus
    have level' : (output.1 : ℝ) ≤ (input.1 : ℝ) + (hplus : ℝ) := by exact_mod_cast level
    have estimate := mul_le_mul_of_nonneg_left level' ht
    simpa only [hi, ho, exponent] using (show t * (output.1 : ℝ) - t * input.1 ≤ t * hplus by nlinarith)
  · apply minus
    have level' : (input.1 : ℝ) + (hminus : ℝ) ≤ (output.1 : ℝ) := by exact_mod_cast level
    have estimate := mul_le_mul_of_nonpos_left level' hs
    simpa only [hi, ho, exponent] using (show s * (output.1 : ℝ) - s * input.1 ≤ s * hminus by nlinarith)
  · rcases level with fromOutput | fromInput
    · apply minus
      have level' : (hminus : ℝ) ≤ (output.1 : ℝ) := by exact_mod_cast fromOutput
      have estimate := mul_le_mul_of_nonpos_left level' hs
      have nonnegative := mul_nonneg ht (Nat.cast_nonneg input.1 : (0 : ℝ) ≤ input.1)
      simpa only [hi, ho, exponent] using (show s * (output.1 : ℝ) - t * input.1 ≤ s * hminus by nlinarith)
    · apply plus
      have level' : -(hplus : ℝ) ≤ (input.1 : ℝ) := by exact_mod_cast fromInput
      have estimate := mul_le_mul_of_nonneg_left level' ht
      have nonpositive := mul_nonpos_of_nonpos_of_nonneg hs (Nat.cast_nonneg output.1 : (0 : ℝ) ≤ output.1)
      simpa only [hi, ho, exponent] using (show s * (output.1 : ℝ) - t * input.1 ≤ t * hplus by nlinarith)
@[expose] def plusThreshold (upper : ℝ) : ℤ := ⌊Real.logb 2 upper⌋ + 6
@[expose] def minusThreshold (lower : ℝ) : ℤ := ⌊Real.logb 2 lower⌋ - 6

private theorem log_power (scale q k : ℝ) (positive : 0 < scale) :
    (2 : ℝ) ^ (q * (Real.logb 2 scale + k)) = (2 : ℝ) ^ (q * k) * scale ^ q := by
  rw [show q * (Real.logb 2 scale + k) = q*k + Real.logb 2 scale*q by ring,
    Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num) (Real.logb 2 scale) q,
    Real.rpow_logb (by norm_num) (by norm_num) positive]

theorem plus_threshold_bound (scale t : ℝ) (positive : 0 < scale) (ht : 0 ≤ t) :
    (2 : ℝ) ^ (t * (plusThreshold scale : ℝ)) ≤ (2 : ℝ) ^ (6*t) * scale ^ t := by
  have floor := Int.floor_le (Real.logb 2 scale)
  have threshold : (plusThreshold scale : ℝ) ≤ Real.logb 2 scale + 6 := by
    change ((⌊Real.logb 2 scale⌋ + 6 : ℤ) : ℝ) ≤ _
    push_cast
    linarith
  calc
    _ ≤ (2 : ℝ) ^ (t * (Real.logb 2 scale + 6)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left threshold ht)
    _ = _ := by rw [log_power scale t 6 positive, mul_comm t 6]

theorem minus_threshold_bound (scale s : ℝ) (positive : 0 < scale) (hs : s ≤ 0) :
    (2 : ℝ) ^ (s * (minusThreshold scale : ℝ)) ≤ (2 : ℝ) ^ (-7*s) * scale ^ s := by
  have floor := Int.lt_floor_add_one (Real.logb 2 scale)
  have threshold : Real.logb 2 scale - 7 ≤ (minusThreshold scale : ℝ) := by
    change _ ≤ ((⌊Real.logb 2 scale⌋ - 6 : ℤ) : ℝ)
    push_cast
    linarith
  calc
    _ ≤ (2 : ℝ) ^ (s * (Real.logb 2 scale + (-7))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by have h := mul_le_mul_of_nonpos_left threshold hs; linarith)
    _ = _ := by rw [log_power scale s (-7) positive, mul_comm s (-7)]

/-- The principal frequency gain has a fixed exponent-dependent constant,
independent of the derivative word and its hyperbolic factors. -/
theorem principal_weight_bound (t s upper lower : ℝ) (ht : 0 ≤ t) (hs : s ≤ 0)
    (upperPositive : 0 < upper) (lowerPositive : 0 < lower)
    (output input : ℕ × Bool)
    (relation : linked (plusThreshold upper) (minusThreshold lower) output input) :
    (2 : ℝ) ^ (exponent t s output.2 * output.1 - exponent t s input.2 * input.1) ≤
      max ((2 : ℝ) ^ (6*t)) ((2 : ℝ) ^ (-7*s)) * max (upper^t) (lower^s) := by
  apply (weight_bound t s ht hs _ _ output input relation).trans
  apply max_le
  · apply (plus_threshold_bound upper t upperPositive ht).trans
    exact mul_le_mul (le_max_left _ _) (le_max_left _ _)
      (Real.rpow_nonneg upperPositive.le _) (le_max_of_le_left (Real.rpow_nonneg (by norm_num) _))
  · apply (minus_threshold_bound lower s lowerPositive hs).trans
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _)
      (Real.rpow_nonneg lowerPositive.le _) (le_max_of_le_left (Real.rpow_nonneg (by norm_num) _))
end LeanShared.BTLinkedDyadicWeights
