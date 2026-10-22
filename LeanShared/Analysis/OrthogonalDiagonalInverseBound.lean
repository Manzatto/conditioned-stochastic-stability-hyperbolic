module
public import LeanShared.Analysis.OrthogonalDiagonalConeBounds

/-! Uniform full inverse bounds of the actual orthogonally encoded
hyperbolic diagonal block, from its two genuine component inverse bounds. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem diagonal_inverse_apply (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y) (z : X×Y) :
    (diagonal dimension U S).symm (equiv dimension z)=equiv dimension (U.symm z.1,S.symm z.2) := by
  apply (diagonal dimension U S).injective
  rw [(diagonal dimension U S).apply_symm_apply,diagonal_apply,U.apply_symm_apply,S.apply_symm_apply]

theorem norm_le_axis_sum (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (z : X×Y) :
    ‖equiv dimension z‖≤‖z.1‖+‖z.2‖ := by
  have decomposition : equiv dimension z=equiv dimension (z.1,0)+equiv dimension (0,z.2) := by
    rw [←map_add]
    congr 1
    exact Prod.ext (add_zero z.1).symm (zero_add z.2).symm
  rw [decomposition]
  exact (norm_add_le _ _).trans_eq (by rw [norm_first_axis,norm_second_axis])

theorem diagonal_inverse_bound (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y) (K : ℝ) (nonnegativeK : 0≤K)
    (unstable : ‖U.symm.toContinuousLinearMap‖≤1/4)
    (stable : ‖S.symm.toContinuousLinearMap‖≤K) :
    ‖(diagonal dimension U S).symm.toContinuousLinearMap‖≤K+1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
  change ‖(diagonal dimension U S).symm (equiv dimension z)‖≤_
  rw [diagonal_inverse_apply]
  have first := (U.symm.toContinuousLinearMap.le_opNorm z.1).trans
    (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))
  have second := (S.symm.toContinuousLinearMap.le_opNorm z.2).trans
    (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have input := axis_norm_le dimension z
  have firstBound := first.trans (mul_le_mul_of_nonneg_left input.1 (by norm_num : (0:ℝ)≤1/4))
  have secondBound := second.trans (mul_le_mul_of_nonneg_left input.2 nonnegativeK)
  have total := norm_le_axis_sum dimension (U.symm z.1,S.symm z.2)
  change ‖equiv dimension (U.symm z.1,S.symm z.2)‖≤‖U.symm z.1‖+‖S.symm z.2‖ at total
  change ‖U.symm z.1‖≤(1/4:ℝ)*‖equiv dimension z‖ at firstBound
  change ‖S.symm z.2‖≤K*‖equiv dimension z‖ at secondBound
  nlinarith [norm_nonneg (equiv dimension z)]

end LeanShared.OrthogonalProductCoordinates
