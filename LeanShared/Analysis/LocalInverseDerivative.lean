module
public import LeanShared.Analysis.InverseDerivativeConvergence

/-! The derivative of an actual local right inverse is the inverse of the
forward derivative, obtained by differentiating the literal inverse law. -/
public section
namespace LeanShared.LocalInverseDerivative
open Filter
open scoped Topology

theorem hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → E) (x : E) (L : E ≃L[ℝ] E)
    (forward : HasFDerivAt f L.toContinuousLinearMap (g x))
    (inverse : DifferentiableAt ℝ g x) (identity : (f ∘ g) =ᶠ[𝓝 x] id) :
    HasFDerivAt g L.symm.toContinuousLinearMap x := by
  have product : L.toContinuousLinearMap * fderiv ℝ g x = 1 := by
    have derivative := identity.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp x forward.differentiableAt inverse,forward.fderiv,fderiv_id] at derivative
    exact derivative
  have eq := Ring.inverse_mul_cancel_left L.toContinuousLinearMap (fderiv ℝ g x) L.toUnit.isUnit
  rw [product,mul_one] at eq
  change Ring.inverse (L.toUnit : E →L[ℝ] E) = fderiv ℝ g x at eq
  rw [Ring.inverse_unit] at eq
  change L.symm.toContinuousLinearMap = fderiv ℝ g x at eq
  rw [eq]
  exact inverse.hasFDerivAt

end LeanShared.LocalInverseDerivative
