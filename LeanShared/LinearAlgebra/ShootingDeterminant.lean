module

public import Mathlib.LinearAlgebra.Determinant

/-! The Jacobian of final-unstable/initial-stable observation is the
unstable principal block of the actual evolution derivative. -/
public noncomputable section
namespace LeanShared.ShootingDeterminant
variable {R U S : Type*} [CommRing R] [AddCommGroup U] [Module R U]
  [AddCommGroup S] [Module R S] [Module.Free R U] [Module.Finite R U]
  [Module.Free R S] [Module.Finite R S]

theorem triangular (A : U × S →ₗ[R] U) :
    (A.prod (LinearMap.snd R U S)).det = (A.comp (LinearMap.inl R U S)).det := by
  classical
  let u := Module.Free.chooseBasis R U
  let s := Module.Free.chooseBasis R S
  have matrix : LinearMap.toMatrix (u.prod s) (u.prod s) (A.prod (LinearMap.snd R U S)) =
      Matrix.fromBlocks (LinearMap.toMatrix u u (A.comp (LinearMap.inl R U S)))
        (LinearMap.toMatrix s u (A.comp (LinearMap.inr R U S))) 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (u.prod s), matrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, LinearMap.det_toMatrix]

end LeanShared.ShootingDeterminant
