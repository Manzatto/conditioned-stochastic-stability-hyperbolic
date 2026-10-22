module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicDerivativeError

/-! Agreement with the actual local C1 chart map gives differentiability
of the constructed radial remainder at every strictly interior orbit point. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open scoped Topology
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

theorem nonlinear_differentiableAt_of_agreement (d : Data U S N) (i : Fin N)
    (H : U × S → U × S) (R : ℝ)
    (agreement : ∀ w, ‖w‖ < R → d.map i w = H w)
    (z : U × S) (inside : ‖z‖ < R) (smooth : DifferentiableAt ℝ H z) :
    DifferentiableAt ℝ (d.nonlinear i) z := by
  have same : d.map i =ᶠ[𝓝 z] H := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds inside] with w hw
    exact agreement w hw
  have differentiable : DifferentiableAt ℝ (d.map i) z := smooth.congr_of_eventuallyEq same
  let block := (d.expanding i).toContinuousLinearMap.prodMap (d.contracting i)
  have expression : d.nonlinear i = d.map i - ⇑block := by
    funext w
    apply Prod.ext
    · change (d.nonlinear i w).1 = (d.expanding i) w.1 + (d.nonlinear i w).1 - (d.expanding i) w.1
      exact (add_sub_cancel_left _ _).symm
    · change (d.nonlinear i w).2 = (d.contracting i) w.2 + (d.nonlinear i w).2 - (d.contracting i) w.2
      exact (add_sub_cancel_left _ _).symm
  rw [expression]
  exact differentiable.sub block.differentiableAt

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
