module
public import LeanShared.Geometry.LinearRechartedDifferential
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The actual change of manifold model induces a homeomorphism of the
total tangent bundles. Its fiber maps are the differentials of the identity,
and conjugate the derivatives of every differentiable map. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.LinearRechartedManifold
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  (e : E ≃L[ℝ] F)

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem identityDifferential_symm_apply (x : M)
     : letI := charts (M := M) e;
    ∀ v : TangentSpace (𝓘(ℝ,F)) x,
    (identityDifferential e x).symm v =
      mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,E)) (@id M) x v := by
  intro v
  rfl

/-- The differential of the actual identity recharting is a homeomorphism
of total tangent spaces, with no additional topology or metric hypothesis. -/
@[expose] def tangentHomeomorph : letI := charts (M := M) e;
    letI := manifold (M := M) e;
    TangentBundle (𝓘(ℝ,E)) M ≃ₜ TangentBundle (𝓘(ℝ,F)) M := by
  letI := charts (M := M) e
  letI := manifold (M := M) e
  exact {
    toFun := fun p => ⟨p.proj, identityDifferential e p.proj p.2⟩
    invFun := fun p => ⟨p.proj, (identityDifferential e p.proj).symm p.2⟩
    left_inv := fun p => by cases p; simp
    right_inv := fun p => by cases p; simp
    continuous_toFun := (identity_forward (M := M) e).continuous_tangentMap (by simp)
    continuous_invFun := (identity_backward (M := M) e).continuous_tangentMap (by simp) }

theorem tangentHomeomorph_apply (p : TangentBundle (𝓘(ℝ,E)) M) :
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    tangentHomeomorph e p = ⟨p.proj, identityDifferential e p.proj p.2⟩ := rfl

theorem tangentHomeomorph_symm_apply : letI := charts (M := M) e;
    letI := manifold (M := M) e;
    ∀ p : TangentBundle (𝓘(ℝ,F)) M,
    (tangentHomeomorph e).symm p =
      ⟨p.proj, (identityDifferential e p.proj).symm p.2⟩ := by
  intro p
  rfl

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem mdifferentiable_rechart {f : M → M}
    (hf : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f) :
    letI := charts (M := M) e;
    MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) f := by
  let := charts (M := M) e
  exact ((identity_forward (M := M) e).mdifferentiable (by simp)).comp
    (hf.comp ((identity_backward (M := M) e).mdifferentiable (by simp)))

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
/-- The original derivative and the derivative in the recharted model are
conjugate by the actual identity differentials. -/
theorem mfderiv_rechart_comp {f : M → M}
    (hf : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f) (x : M) :
    letI := charts (M := M) e;
    (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) f x).comp
        (identityDifferential e x).toContinuousLinearMap =
      (identityDifferential e (f x)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) := by
  let := charts (M := M) e
  have forward := (identity_forward (M := M) e).mdifferentiable (by simp)
  have recharted := mdifferentiable_rechart e hf
  have first := mfderiv_comp x (recharted x) (forward x)
  have second := mfderiv_comp x (forward (f x)) (hf x)
  exact first.symm.trans second

end LeanShared.LinearRechartedManifold
