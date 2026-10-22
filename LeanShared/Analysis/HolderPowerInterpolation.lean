module
public import LeanShared.Analysis.HolderInterpolation
import Mathlib.Tactic.FieldSimp

/-! Quantitative interpolation in the actual Holder graph norm. A common
higher increment bound and uniform bound give an explicit power of the
actual uniform error, including zero error and errors larger than one. -/
public noncomputable section
open scoped BoundedContinuousFunction
namespace LeanShared.HolderInterpolation
variable {X : Type*} [MetricSpace X]

theorem power_norm_bound {a b C B ε : ℝ} (hb : 0≤b) (hab : b<a)
    (hC : 0≤C) (hB : 0≤B) (hε : 0≤ε) (v : BoundedHolderSpace.graph X b)
    (uniform : ‖BoundedHolderSpace.physical X b v‖ ≤ B)
    (error : ‖BoundedHolderSpace.physical X b v‖ ≤ ε)
    (increments : ∀x y,‖BoundedHolderSpace.physical X b v x-
      BoundedHolderSpace.physical X b v y‖ ≤ C*dist x y^a) :
    ‖v‖ ≤ (C+3*B+3)*ε^((a-b)/a) := by
  have ha : 0<a := hb.trans_lt hab
  have exponentPositive : 0<(a-b)/a := div_pos (sub_pos.mpr hab) ha
  have exponentOne : (a-b)/a ≤ 1 := (div_le_one ha).mpr (by linarith)
  by_cases zero : ε=0
  · subst ε
    have physicalZero : BoundedHolderSpace.physical X b v=0 :=
      norm_eq_zero.mp (le_antisymm error (norm_nonneg _))
    have vectorZero : v=0 := BoundedHolderSpace.physical_injective X b (by
      simpa only [map_zero] using physicalZero)
    rw [vectorZero,norm_zero]
    positivity
  have positive : 0<ε := lt_of_le_of_ne hε (Ne.symm zero)
  by_cases small : ε≤1
  · let δ : ℝ := ε^(a⁻¹)
    have hδ : 0<δ := Real.rpow_pos_of_pos positive _
    have firstPower : δ^(a-b)=ε^((a-b)/a) := by
      rw [show δ=ε^(a⁻¹) from rfl,←Real.rpow_mul hε]
      congr 1
      exact mul_comm _ _
    have secondPower : ε/δ^b=ε^((a-b)/a) := by
      rw [show δ=ε^(a⁻¹) from rfl,←Real.rpow_mul hε]
      have equal : (a-b)/a=1-a⁻¹*b := by field_simp
      rw [equal,Real.rpow_sub positive,Real.rpow_one]
    have lowError : ε≤ε^((a-b)/a) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge positive small exponentOne
    have quotientBound : 2*‖BoundedHolderSpace.physical X b v‖/δ^b ≤
        2*ε^((a-b)/a) := by
      calc
        _ ≤ 2*ε/δ^b := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left error (by norm_num)) (Real.rpow_nonneg hδ.le _)
        _ = _ := by rw [mul_div_assoc,secondPower]
    have incrementBound := increment_bound (BoundedHolderSpace.physical X b v) hb hab hC hδ increments
    have graphBound := graph_norm_le b v
      (C:=max (C*δ^(a-b)) (2*‖BoundedHolderSpace.physical X b v‖/δ^b))
      (by positivity) incrementBound
    apply graphBound.trans
    apply max_le
    · have bigger : ε^((a-b)/a) ≤ (C+3*B+3)*ε^((a-b)/a) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hε _) (by linarith)
      exact error.trans (lowError.trans bigger)
    · apply max_le
      · rw [firstPower]
        exact mul_le_mul_of_nonneg_right (by linarith : C≤C+3*B+3) (Real.rpow_nonneg hε _)
      · exact quotientBound.trans (mul_le_mul_of_nonneg_right
          (by linarith : (2:ℝ)≤C+3*B+3) (Real.rpow_nonneg hε _))
  · have large : 1≤ε := (lt_of_not_ge small).le
    have incrementBound := increment_bound (BoundedHolderSpace.physical X b v)
      hb hab hC (δ:=1) (by norm_num) increments
    simp only [Real.one_rpow,div_one,mul_one] at incrementBound
    have graphBound := graph_norm_le b v (C:=max C (2*‖BoundedHolderSpace.physical X b v‖))
      (by positivity) incrementBound
    have crude : ‖v‖ ≤ C+3*B+3 := graphBound.trans (by
      apply max_le
      · linarith
      · apply max_le <;> linarith)
    exact crude.trans (le_mul_of_one_le_right (by linarith : 0≤C+3*B+3)
      (Real.one_le_rpow large exponentPositive.le))
end LeanShared.HolderInterpolation
