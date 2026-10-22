module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-! Actual derivative comparison gives a quantitative image ball by the
Banach inverse argument. The inverse bound is inflated by one so the same
statement includes zero-dimensional source and target spaces. -/
public noncomputable section
namespace LeanShared.SurjectivityFromDerivativeComparison
open Set Metric
open scoped NNReal

theorem surjOn_closedBall
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (L : E ≃L[ℝ] F) (center : E) (radius : ℝ) (nonnegative : 0 ≤ radius)
    (δ : ℝ≥0) (differentiable : ∀ x ∈ closedBall center radius, DifferentiableAt ℝ f x)
    (comparison : ∀ x ∈ closedBall center radius, ‖fderiv ℝ f x - L.toContinuousLinearMap‖ ≤ δ) :
    SurjOn f (closedBall center radius)
      (closedBall (f center) (((‖L.symm.toContinuousLinearMap‖ + 1)⁻¹ - δ) * radius)) := by
  let inverse : L.toContinuousLinearMap.NonlinearRightInverse := {
    toFun := L.symm
    nnnorm := ‖L.symm.toContinuousLinearMap‖₊ + 1
    bound' := by
      intro v
      change ‖L.symm v‖ ≤ (‖L.symm.toContinuousLinearMap‖ + 1) * ‖v‖
      exact (L.symm.toContinuousLinearMap.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v))
    right_inv' := L.apply_symm_apply }
  have approximates : ApproximatesLinearOn f L.toContinuousLinearMap (closedBall center radius) δ := by
    intro x hx y hy
    exact (convex_closedBall center radius).norm_image_sub_le_of_norm_fderiv_le'
      differentiable comparison hy hx
  exact approximates.surjOn_closedBall_of_nonlinearRightInverse inverse nonnegative Subset.rfl

end LeanShared.SurjectivityFromDerivativeComparison
