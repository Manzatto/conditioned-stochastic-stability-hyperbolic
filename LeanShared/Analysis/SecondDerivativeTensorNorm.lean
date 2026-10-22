module
public import LeanShared.Analysis.FirstDerivativeTensorNorm
public import Mathlib.Analysis.Calculus.MeanValue

/-! Literal second derivative tensors and uniform derivative Lipschitz estimates
on convex domains. No extension of a partial coordinate map is used. -/
public noncomputable section
namespace LeanShared.SecondDerivativeTensorNorm
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

@[expose] def tensor : (E→L[ℝ](E→L[ℝ]F))≃ₗᵢ[ℝ](ContinuousMultilinearMap ℝ (fun _:Fin 2=>E) F):=
  (FirstDerivativeTensorNorm.tensor (E:=E) (F:=E→L[ℝ]F)).trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm

theorem tensor_fderiv (f:E→F) (x:E) :
    (tensor (E:=E) (F:=F)) (fderiv ℝ (fderiv ℝ f) x)=iteratedFDeriv ℝ 2 f x :=by
  rw [tensor,LinearIsometryEquiv.trans_apply,FirstDerivativeTensorNorm.tensor_fderiv]
  exact (iteratedFDeriv_succ_eq_comp_right (n:=1) (f:=f) (x:=x)).symm

theorem difference (f g:E→F) (x:E) :
    ‖fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x‖=
      ‖iteratedFDeriv ℝ 2 f x-iteratedFDeriv ℝ 2 g x‖ :=by
  calc
    _ = ‖(tensor (E:=E) (F:=F)) (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x)‖ :=
      ((tensor (E:=E) (F:=F)).norm_map _).symm
    _ = _ :=by
      have eq := (tensor (E:=E) (F:=F)).toLinearEquiv.map_sub
        (fderiv ℝ (fderiv ℝ f) x) (fderiv ℝ (fderiv ℝ g) x)
      change (tensor (E:=E) (F:=F)) (_-_)= (tensor (E:=E) (F:=F)) _-(tensor (E:=E) (F:=F)) _ at eq
      rw [eq,tensor_fderiv,tensor_fderiv]

theorem derivative_difference_lipschitz {f g:E→F} {K:Set E} (convex:Convex ℝ K)
    (df:∀x∈K,DifferentiableAt ℝ (fderiv ℝ f) x)
    (dg:∀x∈K,DifferentiableAt ℝ (fderiv ℝ g) x)
    {B:ℝ} (bound:∀x∈K,‖iteratedFDeriv ℝ 2 f x-iteratedFDeriv ℝ 2 g x‖≤B)
    {x y:E} (hx:x∈K) (hy:y∈K) :
    ‖(fderiv ℝ f x-fderiv ℝ g x)-(fderiv ℝ f y-fderiv ℝ g y)‖≤B*‖x-y‖ :=by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (fun z hz=>(df z hz).sub (dg z hz)) _ convex hy hx
  intro z hz
  rw [fderiv_sub (df z hz) (dg z hz),difference]
  exact bound z hz
end LeanShared.SecondDerivativeTensorNorm
