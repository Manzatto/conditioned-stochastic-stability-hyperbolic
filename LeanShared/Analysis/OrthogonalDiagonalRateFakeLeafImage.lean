module
public import LeanShared.Analysis.OrthogonalDiagonalRatePerturbation
public import LeanShared.Analysis.SplitCoordinateOrthogonalSlopes

/-! The literal stable normal plane supplies admissible planes internally.
The rate-dependent original-derivative radius transports full nonlinear
fake-leaf chord conditions by the proved secant theorem. -/
public noncomputable section
namespace LeanShared.OrthogonalDiagonalRateFakeLeafImage
open Set OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem stable_axis_admissible
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (θ : ℝ) (nonnegative : 0 ≤ θ) :
    SplitCoordinateOrthogonalSlopes.stablePlane (equiv dimension) ∈
      FakeLeafGeometry.admissiblePlanes (ProjectionConeTransversality.cone (firstProjection dimension) θ)
        (Module.finrank ℝ Y) := by
  constructor
  · intro v member
    obtain ⟨z, inside, rfl⟩ := Submodule.mem_map.mp member
    have first : z.1 = 0 := inside.1
    change ‖firstProjection dimension (equiv dimension z)‖ ≤
      θ * ‖equiv dimension z - firstProjection dimension (equiv dimension z)‖
    rw [firstProjection_apply, first]
    have zero : equiv dimension ((0 : X), (0 : Y)) = 0 := by
      exact (equiv dimension).map_zero
    rw [zero, norm_zero]
    exact mul_nonneg nonnegative (norm_nonneg _)
  · unfold SplitCoordinateOrthogonalSlopes.stablePlane
    rw [(equiv dimension).toLinearEquiv.finrank_map_eq]
    rw [(Submodule.prodEquiv _ _).finrank_eq]
    simp [Module.finrank_prod]

/-- A single original-rate tolerance transports every literal fake leaf
on every convex chart domain, including all nonlinear secants. -/
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
      (ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a))
      (Module.finrank ℝ Y) Γ = 0) :
    FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a))
      (Module.finrank ℝ Y) (f '' Γ) = 0 := by
  obtain ⟨positiveRadius, _, small, _⟩ :=
    OrthogonalDiagonalRatePerturbation.radius_bounds a K positive contracting nonnegativeK
  obtain ⟨_, _, _, positiveOpening, _, _⟩ :=
    ProjectionConeRateMargin.scalar_bounds positive contracting
  have planes : (FakeLeafGeometry.admissiblePlanes
      (ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a))
      (Module.finrank ℝ Y)).Nonempty :=
    ⟨_, stable_axis_admissible dimension _ positiveOpening.le⟩
  have actualSmall : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ *
      OrthogonalDiagonalRatePerturbation.radius a K < 1 :=
    ((mul_le_mul_of_nonneg_right inverseBound positiveRadius.le).trans small).trans_lt (by norm_num)
  exact FakeLeafLinearImage.nonlinear_image_zero positiveDimension planes f
    (diagonal dimension U S) s convex positiveRadius.le actualSmall differentiable close
    (fun B comparison => (OrthogonalDiagonalRatePerturbation.preserves_inner_cones dimension a K
      positive contracting nonnegativeK U S stable unstable inverseBound B comparison).2) inside fake

end LeanShared.OrthogonalDiagonalRateFakeLeafImage
