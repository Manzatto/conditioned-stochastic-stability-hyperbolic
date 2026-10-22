module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Smoothness of an actual local inverse, without replacing it by a chosen
inverse-function-theorem map. -/
public section
open Filter
open scoped Topology
namespace LeanShared.ContDiffLocalLeftInverse
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_of_eventually_leftInverse {f : E → F} {g : F → E}
    {a : E} {n : WithTop ℕ∞} {L : E ≃L[ℝ] F}
    (hf : ContDiffAt ℝ n f a) (derivative : HasFDerivAt f (L : E →L[ℝ] F) a) (hn : n ≠ 0)
    (inverse : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    ContDiffAt ℝ n g (f a) := by
  have same := (hf.hasStrictFDerivAt' derivative hn).localInverse_unique inverse
  apply (hf.to_localInverse derivative hn).congr_of_eventuallyEq
  filter_upwards [same] with y hy
  exact hy
end LeanShared.ContDiffLocalLeftInverse
