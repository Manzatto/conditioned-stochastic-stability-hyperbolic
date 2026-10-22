module
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! The literal first derivative tensor is the image of the Frechet
 derivative under an actual linear isometry. Four-point Whitney increments
 therefore have exactly the same norm, without differentiability premises. -/
public noncomputable section
namespace LeanShared.FirstDerivativeTensorNorm
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def tensor : (E→L[ℝ]F)≃ₗᵢ[ℝ](ContinuousMultilinearMap ℝ (fun _:Fin 1=>E) F):=
  (continuousMultilinearCurryFin0 ℝ E (E→L[ℝ]F)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 0 E F).symm

theorem tensor_fderiv (f:E→F) (x:E) : (tensor (E:=E) (F:=F)) (fderiv ℝ f x)=iteratedFDeriv ℝ 1 f x :=by
  ext v
  simp [tensor,iteratedFDeriv_one_apply]

theorem four_increment (f g:E→F) (x y:E) :
    ‖(iteratedFDeriv ℝ 1 f x-iteratedFDeriv ℝ 1 g x)-
      (iteratedFDeriv ℝ 1 f y-iteratedFDeriv ℝ 1 g y)‖=
    ‖(fderiv ℝ f x-fderiv ℝ g x)-(fderiv ℝ f y-fderiv ℝ g y)‖ :=by
  rw [←tensor_fderiv f x,←tensor_fderiv g x,←tensor_fderiv f y,←tensor_fderiv g y,
    ←map_sub,←map_sub,←map_sub,LinearIsometryEquiv.norm_map]
end LeanShared.FirstDerivativeTensorNorm
