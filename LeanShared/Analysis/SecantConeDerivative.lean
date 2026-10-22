module
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual tangent vectors remain in any closed homogeneous cone containing
all sufficiently local secants. -/
public section
namespace LeanShared.SecantConeDerivative
open Set Filter
open scoped Topology
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem {f : X → E} {A : X →L[ℝ] E} {x : X}
    (derivative : HasFDerivAt f A x) {s : Set X} (neighborhood : s ∈ 𝓝 x)
    {C : Set E} (closed : IsClosed C)
    (scale : ∀ a : ℝ, 0 ≤ a → ∀ v ∈ C, a • v ∈ C)
    (secants : ∀ y ∈ s, f y - f x ∈ C) (v : X) : A v ∈ C := by
  have line : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have composed : HasDerivAt (fun t : ℝ => f (x + t • v)) (A v) 0 := by
    exact derivative.comp_hasDerivAt_of_eq 0 line (by simp)
  have limit := composed.tendsto_slope_zero_right
  have localLine : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ s := by
    have continuous : ContinuousAt (fun t : ℝ => x + t • v) 0 := line.continuousAt
    have event : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ s := by
      exact continuous.eventually (by simpa using neighborhood)
    exact event.filter_mono nhdsWithin_le_nhds
  apply closed.mem_of_tendsto limit
  filter_upwards [localLine, self_mem_nhdsWithin] with t ht positive
  simpa only [zero_add, zero_smul, add_zero] using
    scale t⁻¹ (inv_nonneg.mpr (le_of_lt positive)) _ (secants _ ht)
end LeanShared.SecantConeDerivative
