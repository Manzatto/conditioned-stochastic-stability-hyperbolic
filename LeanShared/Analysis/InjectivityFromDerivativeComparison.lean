module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic.Linarith

/-! A uniform actual derivative comparison with an invertible linear map
proves injectivity on a convex coordinate neighborhood. This is a quantitative
local-inverse prerequisite, not an assumed injectivity certificate. -/
public noncomputable section
namespace LeanShared.InjectivityFromDerivativeComparison
open Set

theorem injOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (L : E ≃L[ℝ] F) (s : Set E) (convex : Convex ℝ s)
    (δ : ℝ) (small : ‖L.symm.toContinuousLinearMap‖ * δ < 1)
    (differentiable : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (comparison : ∀ x ∈ s, ‖fderiv ℝ f x - L.toContinuousLinearMap‖ ≤ δ) :
    InjOn f s := by
  intro x hx y hy equal
  have upper := convex.norm_image_sub_le_of_norm_fderiv_le' differentiable comparison hx hy
  rw [equal,sub_self,zero_sub,norm_neg] at upper
  have lower : ‖y - x‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L (y - x)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L (y - x))
  have contract : ‖y - x‖ ≤ (‖L.symm.toContinuousLinearMap‖ * δ) * ‖y - x‖ :=
    lower.trans ((mul_le_mul_of_nonneg_left upper (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)
  have zero : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp zero)).symm

end LeanShared.InjectivityFromDerivativeComparison
