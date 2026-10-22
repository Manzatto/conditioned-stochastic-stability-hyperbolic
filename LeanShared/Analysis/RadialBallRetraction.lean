module
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module

/-! An explicit radial retraction onto a closed ball, with Lipschitz constant
at most two in any real normed space. It extends a small local nonlinear
perturbation without requiring a smooth global cutoff or choosing arbitrary
extensions that could destroy noise-parameter continuity. -/
public noncomputable section
namespace LeanShared.RadialBallRetraction
open scoped NNReal

@[expose] def retract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

theorem norm_retract_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (positive : 0 < R) (x : E) : ‖retract R x‖ ≤ R := by
  have denominator : 0 < max R ‖x‖ := positive.trans_le (le_max_left _ _)
  rw [retract, norm_smul, Real.norm_of_nonneg (div_nonneg positive.le denominator.le)]
  calc
    R / max R ‖x‖ * ‖x‖ ≤ R / max R ‖x‖ * max R ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg positive.le denominator.le)
    _ = R := div_mul_cancel₀ R denominator.ne'

theorem retract_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (positive : 0 < R) {x : E} (inside : ‖x‖ ≤ R) : retract R x = x := by
  rw [retract, max_eq_left inside, div_self positive.ne', one_smul]

private theorem ordered_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (positive : 0 < R) (x y : E) (ordered : ‖x‖ ≤ ‖y‖) :
    dist (retract R x) (retract R y) ≤ 2 * dist x y := by
  let a : ℝ := R / max R ‖x‖
  let b : ℝ := R / max R ‖y‖
  have mx : 0 < max R ‖x‖ := positive.trans_le (le_max_left _ _)
  have my : 0 < max R ‖y‖ := positive.trans_le (le_max_left _ _)
  have order : max R ‖x‖ ≤ max R ‖y‖ := max_le_max le_rfl ordered
  have b_nonnegative : 0 ≤ b := div_nonneg positive.le my.le
  have b_one : b ≤ 1 := (div_le_iff₀ my).mpr (by simp)
  have ba : b ≤ a := div_le_div_of_nonneg_left positive.le mx order
  have identity : (a - b) * max R ‖x‖ = b * (max R ‖y‖ - max R ‖x‖) := by
    dsimp [a, b]
    field_simp
  have max_difference : max R ‖y‖ - max R ‖x‖ ≤ ‖y‖ - ‖x‖ := by
    rcases le_total R ‖x‖ with hx | hx
    · rw [max_eq_right hx, max_eq_right (hx.trans ordered)]
    · rw [max_eq_left hx]
      rcases le_total R ‖y‖ with hy | hy
      · rw [max_eq_right hy]; linarith
      · rw [max_eq_left hy]; linarith
  have coefficient : (a - b) * ‖x‖ ≤ ‖y‖ - ‖x‖ := by
    calc
      _ ≤ (a - b) * max R ‖x‖ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr ba)
      _ = b * (max R ‖y‖ - max R ‖x‖) := identity
      _ ≤ 1 * (max R ‖y‖ - max R ‖x‖) :=
        mul_le_mul_of_nonneg_right b_one (sub_nonneg.mpr order)
      _ ≤ _ := by simpa only [one_mul] using max_difference
  simp only [dist_eq_norm, retract]
  change ‖a • x - b • y‖ ≤ 2 * ‖x - y‖
  have decomposition : a • x - b • y = b • (x - y) + (a - b) • x := by module
  rw [decomposition]
  calc
    _ ≤ ‖b • (x - y)‖ + ‖(a - b) • x‖ := norm_add_le _ _
    _ = b * ‖x - y‖ + (a - b) * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg b_nonnegative,
        Real.norm_of_nonneg (sub_nonneg.mpr ba)]
    _ ≤ 1 * ‖x - y‖ + (‖y‖ - ‖x‖) := add_le_add
      (mul_le_mul_of_nonneg_right b_one (norm_nonneg _)) coefficient
    _ ≤ 2 * ‖x - y‖ := by
      have reverse := norm_sub_norm_le y x
      rw [norm_sub_rev y x] at reverse
      linarith

theorem lipschitz_retract {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (positive : 0 < R) : LipschitzWith 2 (retract (E := E) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total ‖x‖ ‖y‖ with order | order
  · exact ordered_distance R positive x y order
  · simpa only [NNReal.coe_ofNat, dist_comm] using ordered_distance R positive y x order

end LeanShared.RadialBallRetraction
