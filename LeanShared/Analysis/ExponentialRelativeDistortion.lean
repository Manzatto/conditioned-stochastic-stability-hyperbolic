module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! A relative exponential-weight estimate keeps the base weight
explicit and has a uniform coefficient on a bounded increment scale.
-/

public section
namespace LeanShared.ExponentialRelativeDistortion
open Set

theorem bound (x y C δ : ℝ) (nonnegativeC : 0 ≤ C)
    (nonnegativeδ : 0 ≤ δ) (smallδ : δ ≤ 1) (difference : |y - x| ≤ C * δ) :
    |Real.exp y - Real.exp x| ≤ Real.exp x * (Real.exp C * C) * δ := by
  have upperX : x ≤ x + C * δ := le_add_of_nonneg_right (mul_nonneg nonnegativeC nonnegativeδ)
  have upperY : y ≤ x + C * δ := by linarith [le_abs_self (y - x)]
  have derivative : ‖Real.exp y - Real.exp x‖ ≤ Real.exp (x + C * δ) * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
      (fun t ht => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr ht)
      (convex_Iic (x + C * δ)) upperX upperY
  have expBound : Real.exp (x + C * δ) ≤ Real.exp x * Real.exp C := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right nonnegativeC smallδ))
      (Real.exp_pos _).le
  change |Real.exp y - Real.exp x| ≤ Real.exp (x + C * δ) * |y - x| at derivative
  calc
    _ ≤ Real.exp (x + C * δ) * |y - x| := derivative
    _ ≤ (Real.exp x * Real.exp C) * (C * δ) :=
      mul_le_mul expBound difference (abs_nonneg _) (by positivity)
    _ = _ := by ring

end LeanShared.ExponentialRelativeDistortion
