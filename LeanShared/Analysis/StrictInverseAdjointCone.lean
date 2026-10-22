module
public import LeanShared.Analysis.StrictConeLinearAction
public import LeanShared.Analysis.FakeLeafLinearImage
public import Mathlib.Analysis.Normed.Ring.Units

/-! Strict deterministic inverse-adjoint cone action produces a genuine
operator neighborhood for all nearby equivalences. No random cone-action
neighborhood is assumed. -/
public noncomputable section
open Set
namespace LeanShared.StrictInverseAdjointCone
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem inverse_adjoint_eq (A : E ≃L[ℝ] E) :
    (Ring.inverse A.toContinuousLinearMap).adjoint =
      (FakeLeafLinearImage.adjointEquiv A.symm).toContinuousLinearMap := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse, ContinuousLinearMap.inverse_equiv]
  apply ContinuousLinearMap.ext
  intro x
  exact (FakeLeafLinearImage.adjointEquiv_apply A.symm x).symm

private theorem continuousAt_inverse_adjoint (A : E ≃L[ℝ] E) :
    ContinuousAt (fun B : E →L[ℝ] E => (Ring.inverse B).adjoint) A.toContinuousLinearMap := by
  let unit : (E →L[ℝ] E)ˣ :=
    { val := A.toContinuousLinearMap
      inv := A.symm.toContinuousLinearMap
      val_inv := by
        apply ContinuousLinearMap.ext
        intro x
        exact A.apply_symm_apply x
      inv_val := by
        apply ContinuousLinearMap.ext
        intro x
        exact A.symm_apply_apply x }
  have inverse : ContinuousAt Ring.inverse A.toContinuousLinearMap :=
    NormedRing.inverse_continuousAt unit
  exact ContinuousLinearMap.adjoint.continuous.continuousAt.comp inverse

theorem exists_radius {C D : Set E} (closed : IsClosed C)
    (sourceScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (targetZero : (0 : E) ∈ D)
    (targetScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ D, r • v ∈ D)
    (A : E ≃L[ℝ] E)
    (strict : ∀ v ∈ C ∩ Metric.sphere (0 : E) 1,
      FakeLeafLinearImage.adjointEquiv A.symm v ∈ interior D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ B : E ≃L[ℝ] E,
      ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ ≤ δ →
      ∀ v ∈ C, FakeLeafLinearImage.adjointEquiv B.symm v ∈ D := by
  obtain ⟨ρ, positive, action⟩ := StrictConeLinearAction.exists_radius closed sourceScale
    targetZero targetScale (FakeLeafLinearImage.adjointEquiv A.symm).toContinuousLinearMap strict
  obtain ⟨r, rpos, near⟩ := (Metric.continuousAt_iff.mp
    (continuousAt_inverse_adjoint A)) ρ positive
  refine ⟨r / 2, half_pos rpos, fun B close v hv => ?_⟩
  have error := near (x := B.toContinuousLinearMap)
    (show dist B.toContinuousLinearMap A.toContinuousLinearMap < r from by
      rw [dist_eq_norm]
      exact close.trans_lt (half_lt_self rpos))
  rw [dist_eq_norm, inverse_adjoint_eq A, inverse_adjoint_eq B] at error
  exact action (FakeLeafLinearImage.adjointEquiv B.symm).toContinuousLinearMap error.le v hv
/-- Strict deterministic cone action selects one radius which preserves
ALL literal fake leaves for EVERY actual nonlinear map in the derivative
neighborhood on a convex chart domain. -/
theorem exists_image_radius {C D : Set E} {ds : ℕ}
    (positiveDimension : 0 < ds)
    (planes : (FakeLeafGeometry.admissiblePlanes C ds).Nonempty)
    (closed : IsClosed C)
    (sourceScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (targetZero : (0 : E) ∈ D)
    (targetScale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ D, r • v ∈ D)
    (A : E ≃L[ℝ] E)
    (strict : ∀ v ∈ C ∩ Metric.sphere (0 : E) 1,
      FakeLeafLinearImage.adjointEquiv A.symm v ∈ interior D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (f : E → E) (s : Set E), Convex ℝ s →
      (∀ x ∈ s, DifferentiableAt ℝ f x) →
      (∀ x ∈ s, ‖fderiv ℝ f x - A.toContinuousLinearMap‖ ≤ δ) →
      ∀ Γ ⊆ s, FakeLeafGeometry.leafError C ds Γ = 0 →
        FakeLeafGeometry.leafError D ds (f '' Γ) = 0 := by
  obtain ⟨ρ, positive, action⟩ := exists_radius closed sourceScale targetZero targetScale A strict
  let M := ‖A.symm.toContinuousLinearMap‖
  have Mn : 0 ≤ M := norm_nonneg _
  let δ := min ρ (1 / (2 * (M + 1)))
  have δp : 0 < δ := lt_min positive (div_pos zero_lt_one (by linarith))
  have small : M * δ < 1 := by
    have ratio : M / (2 * (M + 1)) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    have estimate := mul_le_mul_of_nonneg_left (min_le_right ρ (1 / (2 * (M + 1)))) Mn
    exact estimate.trans_lt (by simpa only [one_div, ← div_eq_mul_inv] using ratio)
  refine ⟨δ, δp, fun f s convex differentiable comparison Γ inside fake => ?_⟩
  exact FakeLeafLinearImage.nonlinear_image_zero positiveDimension planes f A s convex δp.le
    small differentiable comparison
    (fun B close => action B (close.trans (min_le_left _ _))) inside fake
end LeanShared.StrictInverseAdjointCone
