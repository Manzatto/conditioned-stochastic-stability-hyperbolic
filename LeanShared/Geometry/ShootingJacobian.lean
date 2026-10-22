module

public import LeanShared.LinearAlgebra.ShootingDeterminant
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! The literal final-unstable/initial-stable observation has Jacobian equal
to the unstable principal block of the actual derivative. -/
public noncomputable section
namespace LeanShared.ShootingJacobian
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def observation (F : U × S → U × S) (z : U × S) : U × S := ((F z).1, z.2)

@[expose] def derivative (A : U × S →L[ℝ] U × S) : U × S →L[ℝ] U × S :=
  ((ContinuousLinearMap.fst ℝ U S).comp A).prod (ContinuousLinearMap.snd ℝ U S)

theorem hasFDerivAt {F : U × S → U × S} {z : U × S} {A : U × S →L[ℝ] U × S}
    (h : HasFDerivAt F A z) : HasFDerivAt (observation F) (derivative A) z :=
  h.fst.prodMk hasFDerivAt_snd

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]

theorem determinant (A : U × S →L[ℝ] U × S) :
    (derivative A).det =
      (((ContinuousLinearMap.fst ℝ U S).comp A).comp (ContinuousLinearMap.inl ℝ U S)).det := by
  exact ShootingDeterminant.triangular ((ContinuousLinearMap.fst ℝ U S).comp A).toLinearMap

end LeanShared.ShootingJacobian
