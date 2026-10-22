module

public import LeanShared.Geometry.BundleEndomorphismCoordinates

/-! The actual coordinate norm of a bundle endomorphism is bounded by
its native fiber norm and the two genuine chart norm factors. -/
public noncomputable section
open Bundle
namespace LeanShared.BundleEndomorphismCoordinates
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem norm_le (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (P : ∀ b, E b →L[ℝ] E b) (x : B) (C D : ℝ) (nonnegative : 0 ≤ C)
    (forward : ‖e.continuousLinearMapAt ℝ x‖ ≤ C) (inverse : ‖e.symmL ℝ x‖ ≤ C)
    (native : ‖P x‖ ≤ D) : ‖coordinates E e P x‖ ≤ C ^ 2 * D := by
  unfold coordinates
  calc
    _ ≤ ‖e.continuousLinearMapAt ℝ x‖ * (‖P x‖ * ‖e.symmL ℝ x‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C * (D * C) :=
      mul_le_mul forward (mul_le_mul native inverse (norm_nonneg _) ((norm_nonneg _).trans native))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) nonnegative
    _ = _ := by ring

end LeanShared.BundleEndomorphismCoordinates
