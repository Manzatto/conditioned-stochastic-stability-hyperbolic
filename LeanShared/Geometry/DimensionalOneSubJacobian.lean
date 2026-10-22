module

public import LeanShared.Geometry.NormDetOneSub
public import LeanShared.Geometry.DimensionalJacobianBound

/-! Uniform actual determinant and reciprocal determinant bounds for
norm-small endomorphisms of any Hilbert subspace of bounded dimension. -/
public noncomputable section
namespace LeanShared.DimensionalOneSubJacobian
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

theorem small_bounds (d : ℕ) (dimension : Module.finrank ℝ U ≤ d)
    (A : U →L[ℝ] U) (small : ‖A‖ ≤ (1 / 2 : ℝ)) :
    (ContinuousLinearMap.id ℝ U - A).toLinearMap.normDet ≤ DimensionalJacobianBound.bound d (3 / 2) ∧
      1 ≤ DimensionalJacobianBound.bound d 2 *
        (ContinuousLinearMap.id ℝ U - A).toLinearMap.normDet := by
  constructor
  · have bound := NormDetOneSub.upper A small
    norm_num only at bound
    exact bound.trans (DimensionalJacobianBound.dimension_mono dimension (3 / 2))
  · have bound := NormDetOneSub.reciprocal_bound A (by norm_num : (1 / 2 : ℝ) < 1) small
    norm_num only at bound
    exact bound.trans (mul_le_mul_of_nonneg_right
      (DimensionalJacobianBound.dimension_mono dimension 2) (LinearMap.normDet_nonneg _))

end LeanShared.DimensionalOneSubJacobian
