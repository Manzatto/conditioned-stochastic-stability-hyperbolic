module
public import LeanShared.Geometry.OrthogonalProductCoordinateCalculus
public import LeanShared.Analysis.ProjectionConeUniformMargin

/-! Uniform component estimates for the actual inverse adjoint of an
orthogonally encoded hyperbolic diagonal block. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

@[expose] def firstProjection (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) : E→L[ℝ]E :=
  (equiv dimension).toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ X).prodMap (0 : Y→L[ℝ]Y)).comp (equiv dimension).symm.toContinuousLinearMap)

@[expose] def secondProjection (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) : E→L[ℝ]E :=
  (equiv dimension).toContinuousLinearMap.comp
    (((0 : X→L[ℝ]X).prodMap (ContinuousLinearMap.id ℝ Y)).comp (equiv dimension).symm.toContinuousLinearMap)

theorem firstProjection_apply (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (z : X×Y) :
    firstProjection dimension (equiv dimension z)=equiv dimension (z.1,0) := by
  simp [firstProjection,ContinuousLinearMap.comp_apply]
  rfl

theorem secondProjection_apply (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (z : X×Y) :
    secondProjection dimension (equiv dimension z)=equiv dimension (0,z.2) := by
  simp [secondProjection,ContinuousLinearMap.comp_apply]
  rfl

theorem axis_norm_le (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (z : X×Y) :
    ‖z.1‖≤‖equiv dimension z‖ ∧ ‖z.2‖≤‖equiv dimension z‖ := by
  have equation := inner_map dimension z z
  simp only [real_inner_self_eq_norm_sq] at equation
  constructor
  · nlinarith [norm_nonneg z.1,norm_nonneg (equiv dimension z),sq_nonneg ‖z.2‖]
  · nlinarith [norm_nonneg z.2,norm_nonneg (equiv dimension z),sq_nonneg ‖z.1‖]

theorem projection_bounds (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    ‖firstProjection dimension‖≤1 ∧ ‖secondProjection dimension‖≤1 := by
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [firstProjection_apply,norm_first_axis,one_mul]
    exact (axis_norm_le dimension z).1
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply,norm_second_axis,one_mul]
    exact (axis_norm_le dimension z).2

theorem projections_add (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (v : E) :
    secondProjection dimension v+firstProjection dimension v=v := by
  obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
  rw [firstProjection_apply,secondProjection_apply,←map_add]
  congr 1
  exact Prod.ext (zero_add z.1) (add_zero z.2)

theorem inverse_adjoint_component_bounds
    (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E)
    (U : X≃L[ℝ]X) (S : Y≃L[ℝ]Y)
    (stable : ‖S.toContinuousLinearMap‖≤1/4)
    (unstable : ‖U.symm.toContinuousLinearMap‖≤1/4) :
    (∀v,4*‖secondProjection dimension v‖≤
      ‖secondProjection dimension (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm v)‖) ∧
    (∀v,‖firstProjection dimension (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm v)‖≤
      (1/4:ℝ)*‖firstProjection dimension v‖) := by
  have undo (y : Y) : S.toContinuousLinearMap.adjoint (S.symm.toContinuousLinearMap.adjoint y)=y := by
    have identity : S.toContinuousLinearMap.adjoint.comp S.symm.toContinuousLinearMap.adjoint=
        ContinuousLinearMap.id ℝ Y := by
      rw [←ContinuousLinearMap.adjoint_comp]
      rw [show S.symm.toContinuousLinearMap.comp S.toContinuousLinearMap=ContinuousLinearMap.id ℝ Y from by
        ext v
        exact S.symm_apply_apply v]
      exact ContinuousLinearMap.adjoint_id
    exact congrArg (fun A : Y→L[ℝ]Y => A y) identity
  constructor
  · intro v
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply,inverse_adjoint_apply,secondProjection_apply,norm_second_axis,norm_second_axis]
    have estimate := S.toContinuousLinearMap.adjoint.le_opNorm (S.symm.toContinuousLinearMap.adjoint z.2)
    rw [undo,ContinuousLinearMap.adjoint.norm_map] at estimate
    have bound := estimate.trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
    linarith
  · intro v
    obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
    rw [firstProjection_apply,inverse_adjoint_apply,firstProjection_apply,norm_first_axis,norm_first_axis]
    have estimate := U.symm.toContinuousLinearMap.adjoint.le_opNorm z.1
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))

end LeanShared.OrthogonalProductCoordinates
