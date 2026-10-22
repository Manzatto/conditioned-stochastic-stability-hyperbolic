module
public import LeanShared.Geometry.ImmersionPullbackInner
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The Euclidean Gram form is a genuine smooth quadratic function of the
actual differential; smoothness of a reference metric is not assumed. -/
public noncomputable section
namespace LeanShared.ImmersionPullbackInner
open scoped ContDiff
variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem contDiff_form : ContDiff ℝ ∞ (form (H := H) (F := F)) := by
  unfold form
  fun_prop

end LeanShared.ImmersionPullbackInner
