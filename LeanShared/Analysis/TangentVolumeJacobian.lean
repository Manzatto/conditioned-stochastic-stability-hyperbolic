module

public import LeanShared.Analysis.InvariantDerivativeCocycle
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Intrinsic volume factor of actual tangent restrictions

The absolute determinant of a derivative in isometric tangent frames equals
the intrinsic norm determinant of the actual restricted derivative. Thus the
constructed unstable factor is independent of orthonormal frame choices.
Restrictions between different consecutive tangent fibers compose
multiplicatively, including transported fibers along random words.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.TangentVolumeJacobian

open InvariantDerivativeCocycle

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

theorem abs_det_framedRestriction (A : E →L[ℝ] E) (U V : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V) (hA : MapsTo A U V) :
    |(framedRestriction A U V eU eV hA).det| = (A.restrict hA).toLinearMap.normDet := by
  rw [← LinearMap.normDet_eq_abs_det]
  change ((eV.symm.toLinearEquiv.toLinearMap).comp
    ((A.restrict hA).toLinearMap.comp eU.toLinearEquiv.toLinearMap)).normDet = _
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ eV.toLinearEquiv.finrank_eq,
    LinearMap.normDet_comp_of_finrank_eq _ _ eU.toLinearEquiv.finrank_eq]
  have hU : eU.toLinearEquiv.toLinearMap.normDet = 1 := eU.toLinearIsometry.normDet_eq_one
  have hV : eV.symm.toLinearEquiv.toLinearMap.normDet = 1 := eV.symm.toLinearIsometry.normDet_eq_one
  rw [hU, hV, one_mul, mul_one]

/-- Changing isometric frames does not change the intrinsic Jacobian. -/
theorem abs_det_framedRestriction_eq (A : E →L[ℝ] E) (U V : Submodule ℝ E)
    (eU fU : H ≃ₗᵢ[ℝ] U) (eV fV : H ≃ₗᵢ[ℝ] V) (hA : MapsTo A U V) :
    |(framedRestriction A U V eU eV hA).det| =
      |(framedRestriction A U V fU fV hA).det| := by
  rw [abs_det_framedRestriction, abs_det_framedRestriction]

omit [FiniteDimensional ℝ H] in
theorem restricted_normDet_comp (A B : E →L[ℝ] E) (U V W : Submodule ℝ E)
    (eU : H ≃ₗᵢ[ℝ] U) (eV : H ≃ₗᵢ[ℝ] V)
    (hA : MapsTo A U V) (hB : MapsTo B V W) :
    ((B.comp A).restrict (fun _ hx => hB (hA hx))).toLinearMap.normDet =
      (B.restrict hB).toLinearMap.normDet * (A.restrict hA).toLinearMap.normDet := by
  change ((B.restrict hB).toLinearMap.comp (A.restrict hA).toLinearMap).normDet = _
  exact LinearMap.normDet_comp_of_finrank_eq _ _
    (eU.toLinearEquiv.finrank_eq.symm.trans eV.toLinearEquiv.finrank_eq)

/-- The coefficient's unstable Jacobian is the actual intrinsic volume
factor of the derivative restricted to the unstable tangent fiber. -/
theorem unstableJacobian_eq_normDet (F : E → E) (U : E → Submodule ℝ E)
    (e : ∀ x, H ≃ₗᵢ[ℝ] U x)
    (hInv : ∀ x, MapsTo (fderiv ℝ F x) (U x) (U (F x))) (x : E) :
    unstableJacobian F U e hInv x = ((fderiv ℝ F x).restrict (hInv x)).toLinearMap.normDet :=
  abs_det_framedRestriction (fderiv ℝ F x) (U x) (U (F x)) (e x) (e (F x)) (hInv x)

end LeanShared.TangentVolumeJacobian
