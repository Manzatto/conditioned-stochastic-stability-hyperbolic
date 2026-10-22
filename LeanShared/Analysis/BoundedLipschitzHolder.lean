module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Actual bounded Lipschitz maps are globally Hölder in every order
between zero and one, with an explicit produced constant. -/
public noncomputable section
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedLipschitzHolder
variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

theorem bound (f : X →ᵇ F) {L : NNReal} (lip : LipschitzWith L f)
    {a : ℝ} (ha : 0≤a) (ha1 : a≤1) (x y : X) :
    ‖f x-f y‖≤max (L:ℝ) (2*‖f‖)*dist x y^a := by
  by_cases small : dist x y≤1
  · calc
      _ ≤ (L:ℝ)*dist x y := by simpa only [dist_eq_norm] using lip.dist_le_mul x y
      _ ≤ (L:ℝ)*dist x y^a :=
        mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one dist_nonneg small ha1) L.coe_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · calc
      _ ≤ ‖f x‖+‖f y‖ := norm_sub_le _ _
      _ ≤ 2*‖f‖ := by linarith [f.norm_coe_le_norm x,f.norm_coe_le_norm y]
      _ ≤ (2*‖f‖)*dist x y^a :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (le_of_not_ge small) ha)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
end LeanShared.BoundedLipschitzHolder
