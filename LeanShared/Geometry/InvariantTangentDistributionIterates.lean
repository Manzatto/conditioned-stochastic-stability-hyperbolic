module
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Algebra.Module.Submodule.Map

/-! Literal tangent-distribution invariance propagates to derivatives of all
actual iterates by the manifold chain rule. No separate iterate-cocycle or
iterated invariant-splitting certificate is a source field. -/
public section
namespace LeanShared.InvariantTangentDistributionIterates
open Set IsManifold
open scoped Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem map_iterate
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (f : M → M) (smooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) f)
    (K : Set M) (preserves : MapsTo f K K)
    (S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x))
    (invariant : ∀ x ∈ K,
      (S x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f x).toLinearMap = S (f x))
    (n : ℕ) (x : M) (inside : x ∈ K) :
    (S x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[n]) x).toLinearMap = S (f^[n] x) := by
  have differentiable (m : ℕ) : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[m]) := by
    induction m with
    | zero => exact mdifferentiable_id
    | succ m ih => rw [Function.iterate_succ']; exact smooth.comp ih
  induction n with
  | zero =>
    rw [Function.iterate_zero, mfderiv_id]
    exact Submodule.map_id _
  | succ n ih =>
    rw [Function.iterate_succ', mfderiv_comp x (smooth _) (differentiable n x),
      ContinuousLinearMap.toLinearMap_comp, Submodule.map_comp, ih]
    exact invariant _ (preserves.iterate n inside)

end LeanShared.InvariantTangentDistributionIterates
