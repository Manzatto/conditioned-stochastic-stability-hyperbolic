module
public import LeanShared.Analysis.OrthogonalDiagonalRateConeBounds
public import LeanShared.Analysis.UniformInversePerturbationBounds

/-! A common actual-derivative tolerance preserves both one-step vector
and inverse-adjoint cones for all prototypes with the same inverse bound. -/
public noncomputable section
namespace LeanShared.OrthogonalDiagonalRatePerturbation
open Set OrthogonalProductCoordinates

@[expose] def radius (a K : ℝ) : ℝ :=
  ProjectionConeRateMargin.tolerance a / (4 * (K + 1) ^ 2)

theorem radius_bounds (a K : ℝ) (positive : 0 < a) (contracting : a < 1)
    (nonnegativeK : 0 ≤ K) :
    0 < radius a K ∧ radius a K ≤ ProjectionConeRateMargin.tolerance a ∧
      K * radius a K ≤ 1 / 2 ∧
      2 * K ^ 2 * radius a K ≤ ProjectionConeRateMargin.tolerance a := by
  obtain ⟨positiveTolerance, _, _, _, smallTolerance, _⟩ :=
    ProjectionConeRateMargin.scalar_bounds positive contracting
  have positiveRadius : 0 < radius a K := by unfold radius; positivity
  have normalization : (K + 1) ^ 2 * radius a K =
      ProjectionConeRateMargin.tolerance a / 4 := by
    unfold radius
    field_simp [show K + 1 ≠ 0 by linarith]
  have scaleOne := mul_le_mul_of_nonneg_right
    (show 1 ≤ (K + 1) ^ 2 by nlinarith [sq_nonneg K]) positiveRadius.le
  have scaleK := mul_le_mul_of_nonneg_right
    (show K ≤ (K + 1) ^ 2 by nlinarith [sq_nonneg K]) positiveRadius.le
  have scaleSquare := mul_le_mul_of_nonneg_right
    (show K ^ 2 ≤ (K + 1) ^ 2 by nlinarith) positiveRadius.le
  rw [normalization] at scaleOne scaleK scaleSquare
  refine ⟨positiveRadius, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

/-- One tolerance, depending only on the original rate and common inverse
bound, gives strict action for both the actual derivative and its actual
inverse adjoint. No iterate or noisy-cone source is supplied. -/
theorem strict_actions
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ ≤ K)
    (B : E ≃L[ℝ] E)
    (close : ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤ radius a K) :
    (∀ v : E, v ≠ 0 → v ∈ ProjectionConeTransversality.cone (secondProjection dimension) 1 →
      B v ∈ interior (ProjectionConeTransversality.cone (secondProjection dimension)
        (ProjectionConeRateMargin.opening a))) ∧
    (∀ v : E, v ≠ 0 → v ∈ ProjectionConeTransversality.cone (firstProjection dimension) 1 →
      FakeLeafLinearImage.adjointEquiv B.symm v ∈
        interior (ProjectionConeTransversality.cone (firstProjection dimension)
          (ProjectionConeRateMargin.opening a))) := by
  obtain ⟨positiveRadius, direct, small, inverseSize⟩ :=
    radius_bounds a K positive contracting nonnegativeK
  have inverseError := UniformInversePerturbationBounds.bound
    (diagonal dimension U S) B K (radius a K) nonnegativeK positiveRadius.le small inverseBound close
  have adjointError : ‖(FakeLeafLinearImage.adjointEquiv B.symm).toContinuousLinearMap -
      (FakeLeafLinearImage.adjointEquiv (diagonal dimension U S).symm).toContinuousLinearMap‖ ≤
      ProjectionConeRateMargin.tolerance a := by
    change ‖B.symm.toContinuousLinearMap.adjoint -
      (diagonal dimension U S).symm.toContinuousLinearMap.adjoint‖ ≤ _
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
    exact inverseError.trans inverseSize
  constructor
  · exact vector_strict_rate_cone dimension U S a positive contracting stable unstable
      B.toContinuousLinearMap (close.trans direct)
  · exact inverse_adjoint_strict_rate_cone dimension U S a positive contracting stable unstable
      (FakeLeafLinearImage.adjointEquiv B.symm).toContinuousLinearMap adjointError

/-- The two genuine inner cones meet only at zero, including for rates
arbitrarily close to one. -/
theorem inner_cones_inter
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (a : ℝ) (positive : 0 < a) (contracting : a < 1) :
    ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a) ∩
      ProjectionConeTransversality.cone (secondProjection dimension) (ProjectionConeRateMargin.opening a) =
      ({0} : Set E) := by
  obtain ⟨_, _, below, _, _, _⟩ := ProjectionConeRateMargin.scalar_bounds positive contracting
  have complementFirst (v : E) : v - firstProjection dimension v = secondProjection dimension v :=
    sub_eq_iff_eq_add.mpr (projections_add dimension v).symm
  have complementSecond (v : E) : v - secondProjection dimension v = firstProjection dimension v :=
    sub_eq_iff_eq_add.mpr ((add_comm _ _).trans (projections_add dimension v)).symm
  ext v
  constructor
  · intro member
    have first : ‖firstProjection dimension v‖ ≤ ProjectionConeRateMargin.opening a *
        ‖secondProjection dimension v‖ := by
      simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complementFirst] using member.1
    have second : ‖secondProjection dimension v‖ ≤ ProjectionConeRateMargin.opening a *
        ‖firstProjection dimension v‖ := by
      simpa only [ProjectionConeTransversality.cone, mem_ofPred_eq, complementSecond] using member.2
    apply Set.mem_singleton_iff.mpr
    by_contra nonzero
    have triangle := norm_add_le (secondProjection dimension v) (firstProjection dimension v)
    rw [projections_add] at triangle
    have positiveSum : 0 < ‖secondProjection dimension v‖ + ‖firstProjection dimension v‖ :=
      (norm_pos_iff.mpr nonzero).trans_le triangle
    have gap := mul_pos (sub_pos.mpr below) positiveSum
    nlinarith
  · intro zero
    have equality : v = 0 := Set.mem_singleton_iff.mp zero
    simp [equality, ProjectionConeTransversality.cone]

/-- The same radius preserves the actual chosen inner cones, with the
zero vector handled explicitly. -/
theorem preserves_inner_cones
    (dimension : Module.finrank ℝ (X × Y) = Module.finrank ℝ E)
    (a K : ℝ) (positive : 0 < a) (contracting : a < 1) (nonnegativeK : 0 ≤ K)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a)
    (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a)
    (inverseBound : ‖(diagonal dimension U S).symm.toContinuousLinearMap‖ ≤ K)
    (B : E ≃L[ℝ] E)
    (close : ‖B.toContinuousLinearMap - (diagonal dimension U S).toContinuousLinearMap‖ ≤ radius a K) :
    (∀ v ∈ ProjectionConeTransversality.cone (secondProjection dimension) (ProjectionConeRateMargin.opening a),
      B v ∈ ProjectionConeTransversality.cone (secondProjection dimension) (ProjectionConeRateMargin.opening a)) ∧
    (∀ v ∈ ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a),
      FakeLeafLinearImage.adjointEquiv B.symm v ∈
        ProjectionConeTransversality.cone (firstProjection dimension) (ProjectionConeRateMargin.opening a)) := by
  have strict := strict_actions dimension a K positive contracting nonnegativeK U S stable unstable inverseBound B close
  obtain ⟨_, _, below, _, _, _⟩ := ProjectionConeRateMargin.scalar_bounds positive contracting
  have widen (P : E →L[ℝ] E) (v : E)
      (member : v ∈ ProjectionConeTransversality.cone P (ProjectionConeRateMargin.opening a)) :
      v ∈ ProjectionConeTransversality.cone P 1 := by
    change ‖P v‖ ≤ ProjectionConeRateMargin.opening a * ‖v - P v‖ at member
    change ‖P v‖ ≤ 1 * ‖v - P v‖
    exact member.trans (mul_le_mul_of_nonneg_right below.le (norm_nonneg _))
  constructor
  · intro v member
    by_cases zero : v = 0
    · simp [zero, ProjectionConeTransversality.cone]
    · exact interior_subset (strict.1 v zero (widen _ _ member))
  · intro v member
    by_cases zero : v = 0
    · simp [zero, ProjectionConeTransversality.cone]
    · exact interior_subset (strict.2 v zero (widen _ _ member))

end LeanShared.OrthogonalDiagonalRatePerturbation
