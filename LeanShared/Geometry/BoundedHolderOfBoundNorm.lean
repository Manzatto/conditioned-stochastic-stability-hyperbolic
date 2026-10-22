module
public import LeanShared.Geometry.BoundedHolderCore

/-! The Hölder graph built from a bounded continuous function with a Hölder
bound `C ≥ 0` has norm at most `max ‖f‖ C`. -/
public noncomputable section
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedHolderSpace
variable (X : Type*) [MetricSpace X]

theorem norm_ofBound_le (u : ℝ) (f : X →ᵇ ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ u) : ‖ofBound X u f C h‖ ≤ max ‖f‖ C := by
  change ‖(ofBound X u f C h).val‖ ≤ max ‖f‖ C
  rw [Prod.norm_def]
  apply max_le_max le_rfl
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hC (quotient_bound X u f C h)

end LeanShared.BoundedHolderSpace
