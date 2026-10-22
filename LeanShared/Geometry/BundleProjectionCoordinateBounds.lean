module

public import LeanShared.Geometry.BundleProjectionCocycleCoordinates

/-! Native projected bundle-map bounds imply actual chart-matrix bounds.
The two chart factors are explicit and may come from independently chosen
source and target charts of a finite cover. -/
public noncomputable section
open Bundle
namespace LeanShared.BundleProjectionCocycleCoordinates
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

theorem map_comp_projection (e f : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] [f.IsLinear ℝ] (P : ∀ b, E b →L[ℝ] E b)
    (x y : B) (hx : x ∈ e.baseSet) (A : E x →L[ℝ] E y) :
    (map E e f x y A).comp (BundleEndomorphismCoordinates.coordinates E e P x) =
      (f.continuousLinearMapAt ℝ y).comp ((A.comp (P x)).comp (e.symmL ℝ x)) := by
  ext v
  simp only [map, BundleEndomorphismCoordinates.coordinates, ContinuousLinearMap.comp_apply,
    e.symmL_continuousLinearMapAt hx]

theorem projection_complement (e : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] (P : ∀ b, E b →L[ℝ] E b) (x : B) (hx : x ∈ e.baseSet) :
    BundleEndomorphismCoordinates.coordinates E e (fun b => ContinuousLinearMap.id ℝ (E b) - P b) x =
      ContinuousLinearMap.id ℝ F - BundleEndomorphismCoordinates.coordinates E e P x := by
  ext v
  simp only [BundleEndomorphismCoordinates.coordinates, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, map_sub,
    e.continuousLinearMapAt_symmL hx]

theorem map_comp_projection_norm_le (e f : Trivialization F (TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] [f.IsLinear ℝ] (P : ∀ b, E b →L[ℝ] E b)
    (x y : B) (hx : x ∈ e.baseSet) (A : E x →L[ℝ] E y)
    (C κ : ℝ) (nonnegative : 0 ≤ C)
    (source : ‖e.symmL ℝ x‖ ≤ C) (target : ‖f.continuousLinearMapAt ℝ y‖ ≤ C)
    (native : ‖A.comp (P x)‖ ≤ κ) :
    ‖(map E e f x y A).comp (BundleEndomorphismCoordinates.coordinates E e P x)‖ ≤ C ^ 2 * κ := by
  rw [map_comp_projection E e f P x y hx A]
  calc
    _ ≤ ‖f.continuousLinearMapAt ℝ y‖ * (‖A.comp (P x)‖ * ‖e.symmL ℝ x‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C * (κ * C) := by
      have κnonnegative := (norm_nonneg _).trans native
      exact mul_le_mul target (mul_le_mul native source (norm_nonneg _) κnonnegative)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) nonnegative
    _ = _ := by ring

end LeanShared.BundleProjectionCocycleCoordinates
