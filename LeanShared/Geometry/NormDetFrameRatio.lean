module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Ratios of genuine Gram volumes do not depend on the chosen common
source frame. This includes arbitrary nonorthonormal frames and the
zero-dimensional case, with no determinant-normalization premise. -/
public noncomputable section
namespace LeanShared.NormDetFrameRatio
variable {U V F G : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem eq (A : V →L[ℝ] F) (B : V →L[ℝ] G) (H : U ≃L[ℝ] V) :
    (A.comp H.toContinuousLinearMap).toLinearMap.normDet /
      (B.comp H.toContinuousLinearMap).toLinearMap.normDet =
        A.toLinearMap.normDet / B.toLinearMap.normDet := by
  have nonzero : H.toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr H.injective)
  change (A.toLinearMap.comp H.toLinearMap).normDet /
    (B.toLinearMap.comp H.toLinearMap).normDet = _
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ H.toLinearEquiv.finrank_eq,
    LinearMap.normDet_comp_of_finrank_eq _ _ H.toLinearEquiv.finrank_eq]
  exact mul_div_mul_right _ _ nonzero

theorem log_eq (A : V →L[ℝ] F) (B : V →L[ℝ] G) (H : U ≃L[ℝ] V)
    (injectiveA : Function.Injective A) (injectiveB : Function.Injective B) :
    Real.log (A.toLinearMap.normDet / B.toLinearMap.normDet) =
      Real.log (A.comp H.toContinuousLinearMap).toLinearMap.normDet -
        Real.log (B.comp H.toContinuousLinearMap).toLinearMap.normDet := by
  have nonzeroA : (A.comp H.toContinuousLinearMap).toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr (injectiveA.comp H.injective))
  have nonzeroB : (B.comp H.toContinuousLinearMap).toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr (injectiveB.comp H.injective))
  rw [← eq A B H, Real.log_div nonzeroA nonzeroB]

end LeanShared.NormDetFrameRatio
