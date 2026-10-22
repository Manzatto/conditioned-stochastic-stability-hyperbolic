module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith

/-! Any strict contraction admits a positive Hölder exponent satisfying the
bunching inequality for an arbitrary finite base expansion. The exponent is
chosen below the given actual regularity and below one. -/
public noncomputable section
open Filter
open scoped Topology
namespace LeanShared.BunchedSectionHolder

theorem exists_exponent (q L α : ℝ) (qsmall : q < 1) (Lpositive : 0 < L)
    (αpositive : 0 < α) : ∃ β : ℝ, 0 < β ∧ β ≤ α ∧ β ≤ 1 ∧ q*L^β < 1 := by
  have atZero : q*L^(0 : ℝ)<1 := by simpa only [Real.rpow_zero,mul_one] using qsmall
  have near : ∀ᶠ β : ℝ in 𝓝 0, q*L^β<1 :=
    (continuousAt_const.mul (Real.continuousAt_const_rpow (ne_of_gt Lpositive))).eventually
      (gt_mem_nhds atZero)
  obtain ⟨ε,εpositive,ball⟩ := Metric.mem_nhds_iff.mp near
  let δ := min α (min ε 1)
  have δpositive : 0 < δ := lt_min αpositive (lt_min εpositive zero_lt_one)
  have δα : δ ≤ α := min_le_left _ _
  have δε : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have δone : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ/2,by positivity,by linarith,by linarith,?_⟩
  apply ball
  change dist (δ/2) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity)]
  linarith

end LeanShared.BunchedSectionHolder
