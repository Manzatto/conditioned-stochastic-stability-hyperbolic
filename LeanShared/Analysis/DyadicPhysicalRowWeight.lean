module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact output-frequency weighting of actual principal/nonlinked leaf
integrals. All constants retain their literal nonnegative values. -/
public noncomputable section
namespace LeanShared.DyadicPhysicalRowWeight
open scoped ENNReal NNReal

theorem decay {row : ℝ≥0∞} (C : ℝ≥0) (a b d X : ℝ)
    (bound : row ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)^(-d)) *
      (ENNReal.ofReal ((2 : ℝ)^(-b)) * ENNReal.ofReal X)) :
    ENNReal.ofReal ((2 : ℝ)^a) * row ≤
      ENNReal.ofReal ((C : ℝ) * (2 : ℝ)^(a-b-d) * X) := by
  have powers : (2 : ℝ)^a * ((2 : ℝ)^(-d) * (2 : ℝ)^(-b)) = (2 : ℝ)^(a-b-d) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  refine (mul_le_mul_of_nonneg_left bound (show 0 ≤ ENNReal.ofReal ((2 : ℝ)^a) from bot_le)).trans_eq ?_
  calc
    _ = ENNReal.ofReal ((2 : ℝ)^a * ((C : ℝ) * (2 : ℝ)^(-d) * ((2 : ℝ)^(-b) * X))) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
        ENNReal.ofReal_mul (mul_nonneg C.coe_nonneg (Real.rpow_nonneg (by norm_num) _)),
        ENNReal.ofReal_mul C.coe_nonneg,
        ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ENNReal.ofReal_coe_nnreal]
    _ = _ := by
      congr 1
      calc
        _ = (C : ℝ) * ((2 : ℝ)^a * ((2 : ℝ)^(-d) * (2 : ℝ)^(-b))) * X := by ring
        _ = _ := by rw [powers]

theorem principal {row : ℝ≥0∞} (C : ℝ≥0) (a b X : ℝ)
    (bound : row ≤ (C : ℝ≥0∞) *
      (ENNReal.ofReal ((2 : ℝ)^(-b)) * ENNReal.ofReal X)) :
    ENNReal.ofReal ((2 : ℝ)^a) * row ≤
      ENNReal.ofReal ((C : ℝ) * (2 : ℝ)^(a-b) * X) := by
  have actual := decay C a b 0 X (by simpa only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one, mul_one] using bound)
  simpa only [sub_zero] using actual

end LeanShared.DyadicPhysicalRowWeight
