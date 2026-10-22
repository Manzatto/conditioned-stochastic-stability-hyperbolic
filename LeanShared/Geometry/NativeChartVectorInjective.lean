module

public import LeanShared.Geometry.NativeChartVectorDerivative
public import LeanShared.Geometry.DiffeomorphismDifferential

/-! Genuine immersion differentials remain injective in valid native
source charts and after a differentiable diffeomorphism. -/
public noncomputable section
namespace LeanShared.NativeChartVectorDerivative
open Bundle IsManifold
open scoped Manifold ContDiff
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem coordinateDifferential_injective (f : M → F)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (source x : M) (inside : x ∈ (chartAt E source).source) :
    Function.Injective (coordinateDifferential (E := E) f source x) := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ,E))) source
  have member : x ∈ e.baseSet := by rw [TangentChartTrivialization.baseSet]; exact inside
  have inverseInjective : Function.Injective (e.symmL ℝ x) := by
    rw [← e.symm_continuousLinearEquivAt_eq member]
    exact (e.continuousLinearEquivAt ℝ x member).symm.injective
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).injective.comp
    ((injective x).comp inverseInjective)

omit [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem diffeomorphism_comp_injective (f : M → F)
    (differentiable : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,F)) f)
    (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (T : M ≃ₜ M) (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) :
    Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (f ∘ T) x) := by
  rw [mfderiv_comp x (differentiable (T x)) (forward x)]
  exact (injective (T x)).comp (DiffeomorphismDifferential.differential T forward inverse x).injective

end LeanShared.NativeChartVectorDerivative
