module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

/-! The literal nonlinear Fourier phase has gradient DF*η−ξ. Its
finite orthonormal directional gap is exactly the squared gradient norm. -/
public noncomputable section
open scoped RealInnerProductSpace
namespace LeanShared.NonlinearFourierPhaseGradient
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[expose] def phase (F:E→E) (ξ η:E) (x:E) : ℝ:=-⟪ξ,x⟫+⟪η,F x⟫

theorem derivative {F:E→E} {x:E} (smooth:DifferentiableAt ℝ F x) (ξ η v:E) :
    fderiv ℝ (phase F ξ η) x v=⟪(fderiv ℝ F x).adjoint η-ξ,v⟫ :=by
  have h1:HasFDerivAt (fun y:E=>-⟪ξ,y⟫) (-(innerSL ℝ ξ)) x:=
    (innerSL ℝ ξ).hasFDerivAt.neg
  have h2:HasFDerivAt (fun y:E=>⟪η,F y⟫)
      ((innerSL ℝ η).comp (fderiv ℝ F x)) x:=
    (innerSL ℝ η).hasFDerivAt.comp x smooth.hasFDerivAt
  rw [show fderiv ℝ (phase F ξ η) x=(-(innerSL ℝ ξ))+
      (innerSL ℝ η).comp (fderiv ℝ F x) from (h1.add h2).fderiv]
  change -⟪ξ,v⟫+⟪η,fderiv ℝ F x v⟫=⟪(fderiv ℝ F x).adjoint η-ξ,v⟫
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  ring

theorem squared_frame_gap {ι:Type*} [Fintype ι] (b:OrthonormalBasis ι ℝ E)
    {F:E→E} {x:E} (smooth:DifferentiableAt ℝ F x) (ξ η:E) :
    (∑i,(fderiv ℝ (phase F ξ η) x (b i))^2)=‖(fderiv ℝ F x).adjoint η-ξ‖^2 :=by
  simp_rw [derivative smooth]
  simpa only [Real.norm_eq_abs,sq_abs] using
    b.sum_sq_norm_inner_left ((fderiv ℝ F x).adjoint η-ξ)
end LeanShared.NonlinearFourierPhaseGradient
