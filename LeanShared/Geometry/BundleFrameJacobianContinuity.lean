module

public import LeanShared.Geometry.BundleNormDetContinuity

/-! An actual continuous family of frames determines continuous intrinsic
Jacobian and log-Jacobian functions in arbitrary Riemannian bundle metrics.
The frame need not be orthonormal: its Gram volume is divided out. -/
public noncomputable section
open Set Bundle
namespace LeanShared.BundleFrameJacobianContinuity
variable {X B C F G U : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace C]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]
  (D : C → Type*) [∀ c, NormedAddCommGroup (D c)] [∀ c, InnerProductSpace ℝ (D c)]
  [TopologicalSpace (TotalSpace G D)] [FiberBundle G D] [VectorBundle ℝ G D]
  [IsContinuousRiemannianBundle G D]

theorem continuousOn_normDet (f : X → B) (g : X → C) (K : Set X)
    (S : ∀ x, Submodule ℝ (E (f x)))
    (H : ∀ x, U ≃L[ℝ] S x) (A : ∀ x, S x →L[ℝ] D (g x))
    (frames : ∀ u : U, ContinuousOn (fun x => (⟨f x,(H x u).val⟩ : TotalSpace F E)) K)
    (images : ∀ u : U, ContinuousOn (fun x => (⟨g x,A x (H x u)⟩ : TotalSpace G D)) K) :
    ContinuousOn (fun x => (A x).toLinearMap.normDet) K := by
  let frame (x : X) : U →L[ℝ] E (f x) := (S x).subtypeL.comp (H x).toContinuousLinearMap
  let image (x : X) : U →L[ℝ] D (g x) := (A x).comp (H x).toContinuousLinearMap
  have denominator := BundleNormDetContinuity.continuousOn_normDet E f K frame frames
  have numerator := BundleNormDetContinuity.continuousOn_normDet D g K image images
  have same (x : X) : (A x).toLinearMap.normDet =
      (image x).toLinearMap.normDet / (frame x).toLinearMap.normDet := by
    have frameVolume : (frame x).toLinearMap.normDet=(H x).toLinearMap.normDet := by
      exact (LinearMap.normDet_codRestrict (fun u => (H x u).property)).symm
    have nonzero : (H x).toLinearMap.normDet ≠ 0 := by
      intro zero
      exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
        (LinearMap.ker_eq_bot.mpr (H x).injective)
    change (A x).toLinearMap.normDet =
      ((A x).toLinearMap.comp (H x).toLinearMap).normDet / _
    rw [frameVolume,LinearMap.normDet_comp_of_finrank_eq _ _ (H x).toLinearEquiv.finrank_eq]
    exact (mul_div_cancel_right₀ _ nonzero).symm
  have nonzero (x : X) (_ : x ∈ K) : (frame x).toLinearMap.normDet ≠ 0 := by
    intro zero
    have inj : Function.Injective (frame x) :=
      Subtype.val_injective.comp (H x).injective
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr inj)
  exact (numerator.div denominator nonzero).congr (fun x _ => same x)

end LeanShared.BundleFrameJacobianContinuity
