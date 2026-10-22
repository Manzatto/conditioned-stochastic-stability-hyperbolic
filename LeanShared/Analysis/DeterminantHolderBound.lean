module
public import LeanShared.Analysis.SmoothDeterminant
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual quantitative determinant regularity on bounded sets of matrices.
The Lipschitz constant is constructed from smoothness and finite-dimensional
compactness, and applies to arbitrary parameter families without parameter continuity. -/
public noncomputable section
namespace LeanShared.SmoothDeterminant
open Set Metric
open scoped NNReal ContDiff

theorem exists_lipschitz_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : ℝ) : ∃ K : ℝ≥0, ∀ A D : E →L[ℝ] E, ‖A‖ ≤ B → ‖D‖ ≤ B →
      |A.det - D.det| ≤ K * ‖A - D‖ := by
  obtain ⟨K, bound⟩ := contDiff.contDiffOn.exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) (convex_closedBall (0 : E →L[ℝ] E) B)
    (isCompact_closedBall (0 : E →L[ℝ] E) B)
  refine ⟨K, fun A D hA hD => ?_⟩
  have actual : ‖A.det - D.det‖ ≤ K * ‖A - D‖ :=
    (lipschitzOnWith_iff_norm_sub_le.mp bound)
      (by simpa only [mem_closedBall, dist_zero_right] using hA)
      (by simpa only [mem_closedBall, dist_zero_right] using hD)
  simpa only [Real.norm_eq_abs] using actual

theorem holder_of_operator_bound
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace X] (B H a : ℝ) (family : X → E →L[ℝ] E)
    (bounded : ∀ x, ‖family x‖ ≤ B)
    (holder : ∀ x y, ‖family x - family y‖ ≤ H * dist x y ^ a) :
    ∃ K : ℝ≥0, ∀ x y,
      |(family x).det - (family y).det| ≤ (K * H) * dist x y ^ a := by
  obtain ⟨K, bound⟩ := exists_lipschitz_bound (E := E) B
  refine ⟨K, fun x y => ?_⟩
  exact (bound _ _ (bounded x) (bounded y)).trans
    ((mul_le_mul_of_nonneg_left (holder x y) K.coe_nonneg).trans_eq (mul_assoc _ _ _).symm)

theorem abs_holder_of_operator_bound
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace X] (B H a : ℝ) (family : X → E →L[ℝ] E)
    (bounded : ∀ x, ‖family x‖ ≤ B)
    (holder : ∀ x y, ‖family x - family y‖ ≤ H * dist x y ^ a) :
    ∃ K : ℝ≥0, ∀ x y,
      abs (abs (family x).det - abs (family y).det) ≤ (K * H) * dist x y ^ a := by
  obtain ⟨K, bound⟩ := holder_of_operator_bound B H a family bounded holder
  exact ⟨K, fun x y => (abs_abs_sub_abs_le_abs_sub _ _).trans (bound x y)⟩

end LeanShared.SmoothDeterminant
