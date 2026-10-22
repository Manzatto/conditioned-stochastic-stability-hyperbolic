module

public import LeanShared.Geometry.UnitAddCircleTangentFrame
public import LeanShared.Geometry.FrameRiemannianMetric

/-! The concrete circle frame defines the compatible continuous flat
Riemannian metric. The derivative of the real quotient projection is
an isometry for this metric. -/

@[expose] public noncomputable section
open Bundle
open scoped Bundle Manifold ContDiff
namespace LeanShared.UnitAddCircleManifold

instance flatRiemannianBundle : RiemannianBundle (TangentSpace (𝓘(ℝ, Model)) (M := UnitAddCircle)) :=
  ⟨FrameRiemannianMetric.metric tangentFrame⟩

instance flatContinuousRiemannianBundle :
    IsContinuousRiemannianBundle Model (TangentSpace (𝓘(ℝ, Model)) (M := UnitAddCircle)) :=
  ⟨FrameRiemannianMetric.form tangentFrame,
    FrameRiemannianMetric.continuous_form tangentFrame continuous_coframe, fun _ _ _ => rfl⟩

theorem inner_tangentFrame (x : UnitAddCircle) (r s : ℝ) :
    inner ℝ (tangentFrame x r) (tangentFrame x s) = r * s := by
  change FrameRiemannianMetric.form tangentFrame x (tangentFrame x r) (tangentFrame x s) = _
  simp [mul_comm]

theorem norm_tangentFrame (x : UnitAddCircle) (r : ℝ) : ‖tangentFrame x r‖ = ‖r‖ := by
  have square : ‖tangentFrame x r‖ ^ 2 = ‖r‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_tangentFrame]
    simp [pow_two]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp square

theorem norm_projectionDifferential (t r : ℝ) :
    ‖mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model)) projection t r‖ = ‖r‖ := by
  rw [← tangentFrame_projection]
  exact norm_tangentFrame _ _

end LeanShared.UnitAddCircleManifold
