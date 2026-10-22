module
public import LeanShared.Analysis.ProjectionConeHalfMargin
public import LeanShared.Analysis.OrthogonalDiagonalRateFakeLeafImage

/-! The same original-rate perturbation radius preserves the literal half
cones for the actual derivative and its actual inverse adjoint. In particular
the principal-row half-cone fake-leaf family is preserved by nonlinear secants. -/
public noncomputable section
namespace LeanShared.OrthogonalDiagonalHalfConePerturbation
open Set OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem strict_actions
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ ≤ K)
    (B : E ≃L[ℝ] E)
    (close : ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤
      OrthogonalDiagonalRatePerturbation.radius a K) :
    (∀ v : E, v ≠ 0 → v ∈ ProjectionConeTransversality.cone (secondProjection dimension) (1/2) →
      B v ∈ interior (ProjectionConeTransversality.cone (secondProjection dimension) (1/2))) ∧
    (∀ v : E, v ≠ 0 → v ∈ ProjectionConeTransversality.cone (firstProjection dimension) (1/2) →
      FakeLeafLinearImage.adjointEquiv B.symm v ∈
        interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))) := by
  obtain ⟨positiveRadius, direct, small, inverseSize⟩ :=
    OrthogonalDiagonalRatePerturbation.radius_bounds a K positive contracting nonnegativeK
  have inverseError := UniformInversePerturbationBounds.bound
    (diagonal dimension U S) B K (OrthogonalDiagonalRatePerturbation.radius a K)
    nonnegativeK positiveRadius.le small inverseBound close
  have adjointError : ‖(FakeLeafLinearImage.adjointEquiv B.symm).toContinuousLinearMap -
      (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm).toContinuousLinearMap‖ ≤
      ProjectionConeRateMargin.tolerance a := by
    change ‖B.symm.toContinuousLinearMap.adjoint -
      (diagonal dimension U S).symm.toContinuousLinearMap.adjoint‖ ≤ _
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
    exact inverseError.trans inverseSize
  constructor
  · obtain ⟨lower, upper⟩ := vector_rate_component_bounds dimension U S a stable unstable
    exact ProjectionConeHalfMargin.strict_action (firstProjection dimension) (secondProjection dimension)
      (diagonal dimension U S).toContinuousLinearMap B.toContinuousLinearMap a positive contracting
      (fun w => (add_comm _ _).trans (projections_add dimension w))
      (projection_bounds dimension).1 (projection_bounds dimension).2 lower upper (close.trans direct)
  · obtain ⟨lower, upper⟩ := inverse_adjoint_rate_component_bounds dimension U S a stable unstable
    exact ProjectionConeHalfMargin.strict_action (secondProjection dimension) (firstProjection dimension)
      (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm).toContinuousLinearMap
      (FakeLeafLinearImage.adjointEquiv B.symm).toContinuousLinearMap a positive contracting
      (projections_add dimension) (projection_bounds dimension).2 (projection_bounds dimension).1
      lower upper adjointError

theorem preserves_half_cones
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ ≤ K)
    (B : E ≃L[ℝ] E)
    (close : ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤
      OrthogonalDiagonalRatePerturbation.radius a K) :
    (∀ v ∈ ProjectionConeTransversality.cone (secondProjection dimension) (1/2),
      B v ∈ ProjectionConeTransversality.cone (secondProjection dimension) (1/2)) ∧
    (∀ v ∈ ProjectionConeTransversality.cone (firstProjection dimension) (1/2),
      FakeLeafLinearImage.adjointEquiv B.symm v ∈
        ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) := by
  have actions := strict_actions dimension a K positive contracting nonnegativeK U S stable unstable inverseBound B close
  constructor
  · intro v member
    by_cases zero : v = 0
    · simp [zero, ProjectionConeTransversality.cone]
    · exact interior_subset (actions.1 v zero member)
  · intro v member
    by_cases zero : v = 0
    · simp [zero, ProjectionConeTransversality.cone]
    · exact interior_subset (actions.2 v zero member)

/-- Exact half-cone fake leaves, including their nonlinear chord condition,
are transported using the very same derivative radius. -/
theorem nonlinear_image_zero
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (positiveDimension : 0 < Module.finrank ℝ Y)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ ≤ K)
    (f : E → E) (s : Set E) (convex : Convex ℝ s)
    (differentiable : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (close : ∀ x ∈ s, ‖fderiv ℝ f x - (diagonal dimension U S).toContinuousLinearMap‖ ≤
      OrthogonalDiagonalRatePerturbation.radius a K)
    {Γ : Set E} (inside : Γ ⊆ s)
    (fake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))
      (Module.finrank ℝ Y) Γ = 0) :
    FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))
      (Module.finrank ℝ Y) (f '' Γ) = 0 := by
  obtain ⟨positiveRadius, _, small, _⟩ :=
    OrthogonalDiagonalRatePerturbation.radius_bounds a K positive contracting nonnegativeK
  have planes : (FakeLeafGeometry.admissiblePlanes
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))
      (Module.finrank ℝ Y)).Nonempty :=
    ⟨_, OrthogonalDiagonalRateFakeLeafImage.stable_axis_admissible dimension (1/2) (by norm_num)⟩
  have actualSmall : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ *
      OrthogonalDiagonalRatePerturbation.radius a K < 1 :=
    ((mul_le_mul_of_nonneg_right inverseBound positiveRadius.le).trans small).trans_lt (by norm_num)
  exact FakeLeafLinearImage.nonlinear_image_zero positiveDimension planes f
    (diagonal dimension U S) s convex positiveRadius.le actualSmall differentiable close
    (fun B comparison => (preserves_half_cones dimension a K positive contracting nonnegativeK
      U S stable unstable inverseBound B comparison).2) inside fake

end LeanShared.OrthogonalDiagonalHalfConePerturbation
