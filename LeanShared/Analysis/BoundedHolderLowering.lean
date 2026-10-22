module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! Lowering a quantitative Holder bound on an arbitrary set, using a
separate value bound for pairs at distance at least one. -/
public noncomputable section
namespace LeanShared.BoundedHolderLowering
variable {E F:Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem bound {a b B C:ℝ} (ha:0≤a) (lower:a≤b) (hB:0≤B) (hC:0≤C)
    {K:Set E} {f:E→F} (value:∀x∈K,‖f x‖≤B)
    (holder:∀x∈K,∀y∈K,‖f x-f y‖≤C*‖x-y‖^b) :
    ∀x∈K,∀y∈K,‖f x-f y‖≤(C+2*B)*‖x-y‖^a :=by
  intro x hx y hy
  by_cases small:‖x-y‖≤1
  · exact (holder x hx y hy).trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) small ha lower) hC).trans
        (mul_le_mul_of_nonneg_right (by linarith : C≤C+2*B) (Real.rpow_nonneg (norm_nonneg _) _)))
  · have large:1≤‖x-y‖:=le_of_lt (lt_of_not_ge small)
    have power:1≤‖x-y‖^a:=Real.one_le_rpow large ha
    calc
      _ ≤ ‖f x‖+‖f y‖:=norm_sub_le _ _
      _ ≤ 2*B:=by linarith [value x hx,value y hy]
      _ ≤ C+2*B:=by linarith
      _ ≤ (C+2*B)*‖x-y‖^a:=by nlinarith [mul_nonneg (show 0≤C+2*B by positivity) (sub_nonneg.mpr power)]
end LeanShared.BoundedHolderLowering
