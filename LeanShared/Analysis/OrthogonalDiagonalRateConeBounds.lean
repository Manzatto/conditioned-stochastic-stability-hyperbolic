module
public import LeanShared.Analysis.OrthogonalDiagonalConeBounds
public import LeanShared.Analysis.ProjectionConeRateMargin

/-! Actual Hilbert orthogonal-axis estimates for an arbitrary one-step
hyperbolic rate, in both the vector and inverse-adjoint directions. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem vector_rate_component_bounds
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (a : ℝ)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a) :
    (∀ v, ‖firstProjection dimension v‖ ≤
      a * ‖firstProjection dimension (diagonal dimension U S v)‖) ∧
    (∀ v, ‖secondProjection dimension (diagonal dimension U S v)‖ ≤
      a * ‖secondProjection dimension v‖) := by
  constructor
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [firstProjection_apply, diagonal_apply, firstProjection_apply,
      norm_first_axis, norm_first_axis]
    have estimate := U.symm.toContinuousLinearMap.le_opNorm (U z.1)
    rw [show U.symm.toContinuousLinearMap (U z.1) = z.1 from U.symm_apply_apply z.1] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply, diagonal_apply, secondProjection_apply,
      norm_second_axis, norm_second_axis]
    exact (S.toContinuousLinearMap.le_opNorm z.2).trans
      (mul_le_mul_of_nonneg_right stable (norm_nonneg _))

theorem inverse_adjoint_rate_component_bounds
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (a : ℝ)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a) :
    (∀ v, ‖secondProjection dimension v‖ ≤ a *
      ‖secondProjection dimension (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm v)‖) ∧
    (∀ v, ‖firstProjection dimension
      (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm v)‖ ≤
      a * ‖firstProjection dimension v‖) := by
  have undo (y : Y) : S.toContinuousLinearMap.adjoint
      (S.symm.toContinuousLinearMap.adjoint y) = y := by
    have identity : S.toContinuousLinearMap.adjoint.comp S.symm.toContinuousLinearMap.adjoint =
        ContinuousLinearMap.id ℝ Y := by
      rw [← ContinuousLinearMap.adjoint_comp]
      rw [show S.symm.toContinuousLinearMap.comp S.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ Y from by ext v; exact S.symm_apply_apply v]
      exact ContinuousLinearMap.adjoint_id
    exact congrArg (fun A : Y →L[ℝ] Y => A y) identity
  constructor
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply, inverse_adjoint_apply, secondProjection_apply,
      norm_second_axis, norm_second_axis]
    have estimate := S.toContinuousLinearMap.adjoint.le_opNorm
      (S.symm.toContinuousLinearMap.adjoint z.2)
    rw [undo, ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [firstProjection_apply, inverse_adjoint_apply, firstProjection_apply,
      norm_first_axis, norm_first_axis]
    have estimate := U.symm.toContinuousLinearMap.adjoint.le_opNorm z.1
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))

theorem vector_strict_rate_cone
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (a : ℝ)
    (positive : 0 < a) (contracting : a < 1)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (B : E →L[ℝ] E)
    (close : ‖B - (diagonal dimension U S).toContinuousLinearMap‖ ≤ ProjectionConeRateMargin.tolerance a)
    (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone (secondProjection dimension) 1) :
    B v ∈ interior (ProjectionConeTransversality.cone (secondProjection dimension)
      (ProjectionConeRateMargin.opening a)) := by
  obtain ⟨lower, upper⟩ := vector_rate_component_bounds dimension U S a stable unstable
  exact ProjectionConeRateMargin.strict_action (firstProjection dimension) (secondProjection dimension)
    (diagonal dimension U S).toContinuousLinearMap B a positive contracting
    (fun w => (add_comm _ _).trans (projections_add dimension w))
    (projection_bounds dimension).1 (projection_bounds dimension).2 lower upper close v nonzero member

theorem inverse_adjoint_strict_rate_cone
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (a : ℝ)
    (positive : 0 < a) (contracting : a < 1)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (B : E →L[ℝ] E)
    (close : ‖B - (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm).toContinuousLinearMap‖ ≤
      ProjectionConeRateMargin.tolerance a)
    (v : E) (nonzero : v ≠ 0)
    (member : v ∈ ProjectionConeTransversality.cone (firstProjection dimension) 1) :
    B v ∈ interior (ProjectionConeTransversality.cone (firstProjection dimension)
      (ProjectionConeRateMargin.opening a)) := by
  obtain ⟨lower, upper⟩ := inverse_adjoint_rate_component_bounds dimension U S a stable unstable
  exact ProjectionConeRateMargin.strict_action (secondProjection dimension) (firstProjection dimension)
    (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm).toContinuousLinearMap
    B a positive contracting (projections_add dimension)
    (projection_bounds dimension).2 (projection_bounds dimension).1 lower upper close v nonzero member

end LeanShared.OrthogonalProductCoordinates
