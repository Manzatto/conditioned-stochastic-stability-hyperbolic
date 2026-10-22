module

public import LeanShared.Dynamics.ToralCatMapTangentFrame

/-! A compatible continuous flat Riemannian metric on the actual torus
in the genuine Hilbert chart model. -/

@[expose] public noncomputable section
open Bundle
open scoped Bundle Manifold
namespace LeanShared.ToralCatMap

instance flatRiemannianBundle : RiemannianBundle (TangentSpace (𝓘(ℝ, HilbertModel)) (M := Torus)) :=
  ⟨FrameRiemannianMetric.metric tangentFrame⟩

instance flatContinuousRiemannianBundle :
    IsContinuousRiemannianBundle HilbertModel (TangentSpace (𝓘(ℝ, HilbertModel)) (M := Torus)) :=
  ⟨FrameRiemannianMetric.form tangentFrame,
    FrameRiemannianMetric.continuous_form tangentFrame continuous_coframe, fun _ _ _ => rfl⟩

theorem inner_tangentFrame (x : Torus) (v w : LiftHilbert) :
    inner ℝ (tangentFrame x v) (tangentFrame x w) = inner ℝ v w := by
  change FrameRiemannianMetric.form tangentFrame x (tangentFrame x v) (tangentFrame x w) = _
  simp

theorem norm_tangentFrame (x : Torus) (v : LiftHilbert) : ‖tangentFrame x v‖ = ‖v‖ := by
  have square : ‖tangentFrame x v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_tangentFrame, real_inner_self_eq_norm_sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp square

end LeanShared.ToralCatMap
