module
public import LeanShared.Geometry.DiffeomorphismDifferential
import all LeanShared.Geometry.DiffeomorphismDifferential

/-! The inverse of the constructed actual differential is exactly the actual
inverse-map differential. This is an identity, not an independent inverse
cocycle comparison source. -/
public noncomputable section
namespace LeanShared.DiffeomorphismDifferential
open IsManifold
open scoped Manifold

theorem differential_symm_apply
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (v : TangentSpace (𝓘(ℝ, E)) (T x)) :
    (differential T forward inverse x).symm v =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm (T x) v := rfl

end LeanShared.DiffeomorphismDifferential
