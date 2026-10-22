module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exponential Jensen for a positive weight: `∫ w F ≤ (∫ w) (log ∫ w e^F - log ∫ w)`. It follows
from `1 + y ≤ e^y` applied to `y = F - c` with `c` the weighted mean of `F`. -/
public section
open MeasureTheory Real
namespace LeanShared.WeightedExponentialJensen

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

theorem jensen (w F : X → ℝ) (hw : ∀ x, 0 ≤ w x) (wInt : Integrable w ν)
    (wFInt : Integrable (fun x => w x * F x) ν)
    (wExpInt : Integrable (fun x => w x * exp (F x)) ν) (pos : 0 < ∫ x, w x ∂ν) :
    ∫ x, w x * F x ∂ν ≤ (∫ x, w x ∂ν) * (log (∫ x, w x * exp (F x) ∂ν) - log (∫ x, w x ∂ν)) := by
  set W := ∫ x, w x ∂ν
  set I := ∫ x, w x * F x ∂ν
  set Y := ∫ x, w x * exp (F x) ∂ν
  set c := I / W
  have pointwise : ∀ x, w x * (1 + (F x - c)) ≤ w x * exp (F x) * exp (-c) := fun x => by
    have := add_one_le_exp (F x - c)
    rw [mul_assoc, ← exp_add, ← sub_eq_add_neg]
    exact mul_le_mul_of_nonneg_left (by linarith) (hw x)
  have shape : (fun x => w x * (1 + (F x - c))) = fun x => (w x + w x * F x) - c * w x := by
    funext x
    ring
  have lhsInt : Integrable (fun x => w x * (1 + (F x - c))) ν := by
    rw [shape]
    exact (wInt.add wFInt).sub (wInt.const_mul c)
  have lhs : ∫ x, w x * (1 + (F x - c)) ∂ν = W := by
    have sumInt : Integrable (fun x => w x + w x * F x) ν := wInt.add wFInt
    rw [shape, integral_sub sumInt (wInt.const_mul c), integral_add wInt wFInt,
      integral_const_mul]
    change W + I - I / W * W = W
    field_simp
    ring
  have rhs : ∫ x, w x * exp (F x) * exp (-c) ∂ν = Y * exp (-c) := integral_mul_const _ _
  have integrated : W ≤ Y * exp (-c) := by
    rw [← lhs, ← rhs]
    exact integral_mono lhsInt (wExpInt.mul_const _) pointwise
  have scaled : W * exp c ≤ Y := by
    have := mul_le_mul_of_nonneg_right integrated (exp_pos c).le
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] at this
  have Ypos : 0 < Y := lt_of_lt_of_le (mul_pos pos (exp_pos c)) scaled
  have logs : log W + c ≤ log Y := by
    have := log_le_log (mul_pos pos (exp_pos c)) scaled
    rwa [log_mul pos.ne' (exp_pos c).ne', log_exp] at this
  have Ieq : I = c * W := by
    simp only [c]
    field_simp
  rw [Ieq]
  nlinarith [pos]

end LeanShared.WeightedExponentialJensen
