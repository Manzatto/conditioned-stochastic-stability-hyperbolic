module
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Bijectivity of the actual derivative in fixed smooth coordinates is
exactly bijectivity of the manifold differential, with all tangent casts
and chart differentials accounted for by genuine equivalences. -/
public noncomputable section
namespace LeanShared.ChartDerivativeBijectivity
open Set IsManifold
open scoped Manifold

theorem of_coordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (H : M → M) (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (hd : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (x : M) (inside : x ∈ c.source) (target : H x ∈ d.source)
    (smooth : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (bijective : Function.Bijective (fderiv ℝ (d ∘ H ∘ c.symm) (c x))) :
    Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x) := by
  let C := hc.mfderiv inside
  let D := hd.mfderiv target
  let input := (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.trans C.symm
  let output := D.trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x)))
  have source : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) c.symm (c x) C.symm.toContinuousLinearMap :=
    (hc.mdifferentiableAt_symm (c.map_source inside)).hasMFDerivAt
  have middle : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H (c.symm (c x))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x) := by
    rw [c.left_inv inside]
    exact smooth.hasMFDerivAt
  have last : HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) d (H (c.symm (c x))) D.toContinuousLinearMap := by
    rw [c.left_inv inside]
    exact (hd.mdifferentiableAt target).hasMFDerivAt
  have raw := (last.comp (c x) (middle.comp (c x) source)).hasFDerivAt
  have identity : fderiv ℝ (d ∘ H ∘ c.symm) (c x) =
      output.toContinuousLinearMap.comp ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x).comp input.toContinuousLinearMap) := by
    have actual : HasFDerivAt (d ∘ H ∘ c.symm)
        (output.toContinuousLinearMap.comp ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x).comp input.toContinuousLinearMap)) (c x) := raw
    exact actual.fderiv
  rw [identity] at bijective
  have normalized : Function.Bijective ((output ∘ (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)) ∘ input) := bijective
  have physical := (Function.Bijective.of_comp_iff (output ∘ (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)) input.bijective).mp normalized
  exact (Function.Bijective.of_comp_iff' output.bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)).mp physical

end LeanShared.ChartDerivativeBijectivity
