module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicDifferential

/-! The derivative remainder of the constructed finite shooting dynamics
is bounded by its proved nonlinear Lipschitz constant. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

theorem derivative_error (d : Data U S N) (i : Fin N) (z : U × S)
    (smooth : DifferentiableAt ℝ (d.nonlinear i) z) :
    ‖fderiv ℝ (d.map i) z - (d.expanding i).toContinuousLinearMap.prodMap (d.contracting i)‖ ≤
      (d.δ : ℝ) := by
  let block := (d.expanding i).toContinuousLinearMap.prodMap (d.contracting i)
  have expression : d.map i = ⇑block + d.nonlinear i := by
    funext v
    rfl
  rw [expression, fderiv_add block.differentiableAt smooth, block.fderiv, add_sub_cancel_left]
  exact norm_fderiv_le_of_lipschitz ℝ (d.nonlinear_bound i)

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
