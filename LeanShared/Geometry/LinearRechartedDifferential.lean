module

public import LeanShared.Geometry.LinearRechartedIdentity
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The differential of the actual identity recharting is an invertible
linear map, constructed from its smooth forward and inverse maps. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.LinearRechartedManifold
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : E ≃L[ℝ] F)

@[expose] def identityDifferential (x : M) : letI := charts (M := M) e;
    TangentSpace (𝓘(ℝ,E)) x ≃L[ℝ] TangentSpace (𝓘(ℝ,F)) x := by
  letI := charts (M := M) e
  let homeo : M ≃ₜ M := Homeomorph.refl M
  have h : homeo.toOpenPartialHomeomorph.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,F)) :=
    ⟨fun y _ => ((identity_forward (M := M) e).mdifferentiable (by simp) y).mdifferentiableWithinAt,
     fun y _ => ((identity_backward (M := M) e).mdifferentiable (by simp) y).mdifferentiableWithinAt⟩
  exact h.mfderiv (mem_univ x)

theorem identityDifferential_apply (x : M) (v : TangentSpace (𝓘(ℝ,E)) x) :
    letI := charts (M := M) e;
    identityDifferential e x v = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (@id M) x v := rfl

end LeanShared.LinearRechartedManifold
