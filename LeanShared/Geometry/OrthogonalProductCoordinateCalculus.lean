module
public import LeanShared.Geometry.OrthogonalProductCoordinates
public import LeanShared.Analysis.FakeLeafLinearImage

/-! Exact Hilbert calculations for the constructed orthogonal axis
coordinates, retaining the actual max-product norm on the coordinate side. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem inner_map (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (z w : X×Y) :
    inner ℝ (equiv dimension z) (equiv dimension w)=inner ℝ z.1 w.1+inner ℝ z.2 w.2 := by
  change inner ℝ (hilbertEquiv dimension (WithLp.toLp 2 z))
    (hilbertEquiv dimension (WithLp.toLp 2 w))=_
  rw [(hilbertEquiv dimension).inner_map_map]
  rfl

theorem norm_first_axis (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (x : X) :
    ‖equiv dimension (x,0)‖=‖x‖ := by
  have equal := inner_map dimension (x,0) (x,0)
  simp only [real_inner_self_eq_norm_sq,inner_zero_left,add_zero] at equal
  nlinarith [norm_nonneg (equiv dimension (x,0)),norm_nonneg x]

theorem norm_second_axis (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (y : Y) :
    ‖equiv dimension (0,y)‖=‖y‖ := by
  have equal := inner_map dimension (0,y) (0,y)
  simp only [real_inner_self_eq_norm_sq,inner_zero_left,zero_add] at equal
  nlinarith [norm_nonneg (equiv dimension (0,y)),norm_nonneg y]

@[expose] def diagonal (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y) : E≃L[ℝ]E :=
  (equiv dimension).symm.trans ((U.prodCongr S).trans (equiv dimension))

theorem diagonal_apply (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y) (z : X×Y) :
    diagonal dimension U S (equiv dimension z)=equiv dimension (U z.1,S z.2) := by
  change equiv dimension (U ((equiv dimension).symm (equiv dimension z)).1,
    S ((equiv dimension).symm (equiv dimension z)).2)=_
  rw [(equiv dimension).symm_apply_apply]

theorem inverse_adjoint_apply (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y) (z : X×Y) :
    FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm (equiv dimension z)=
      equiv dimension (U.symm.toContinuousLinearMap.adjoint z.1,S.symm.toContinuousLinearMap.adjoint z.2) := by
  apply ext_inner_left ℝ
  intro w
  obtain ⟨v,rfl⟩ := (equiv dimension).surjective w
  rw [FakeLeafLinearImage.adjointEquiv_apply,ContinuousLinearMap.adjoint_inner_right]
  have inverseApply : (diagonal dimension U S).symm (equiv dimension v)=
      equiv dimension (U.symm v.1,S.symm v.2) := by
    apply (diagonal dimension U S).injective
    rw [(diagonal dimension U S).apply_symm_apply,diagonal_apply,U.apply_symm_apply,S.apply_symm_apply]
  change inner ℝ ((diagonal dimension U S).symm (equiv dimension v)) (equiv dimension z)=_
  rw [inverseApply,inner_map,inner_map,ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

end LeanShared.OrthogonalProductCoordinates
