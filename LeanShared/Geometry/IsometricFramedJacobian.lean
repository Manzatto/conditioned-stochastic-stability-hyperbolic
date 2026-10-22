module

public import Mathlib.Analysis.InnerProductSpace.NormDet

/-! Isometric source/target frames identify the absolute determinant of
actual coordinates with the native Riemannian norm determinant. -/
public noncomputable section
namespace LeanShared.IsometricFramedJacobian
variable {U V W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]

theorem eq_normDet (e : U ≃ₗᵢ[ℝ] V) (f : U ≃ₗᵢ[ℝ] W)
    (A : V →ₗ[ℝ] W) (L : U →ₗ[ℝ] U)
    (action : ∀ v, f (L v) = A (e v)) : |L.det| = A.normDet := by
  have equality : f.toLinearEquiv.toLinearMap.comp L = A.comp e.toLinearEquiv.toLinearMap := by
    ext v
    exact action v
  have fvolume : f.toLinearEquiv.toLinearMap.normDet = 1 := f.toLinearIsometry.normDet_eq_one
  have evolume : e.toLinearEquiv.toLinearMap.normDet = 1 := e.toLinearIsometry.normDet_eq_one
  have volumes := congrArg LinearMap.normDet equality
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ rfl,
    LinearMap.normDet_comp_of_finrank_eq _ _ e.toLinearEquiv.finrank_eq,
    fvolume, evolume,
    one_mul, mul_one, LinearMap.normDet_eq_abs_det] at volumes
  exact volumes

end LeanShared.IsometricFramedJacobian
