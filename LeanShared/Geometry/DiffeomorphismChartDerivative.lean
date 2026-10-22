module
public import LeanShared.Geometry.DiffeomorphismInverseDifferential

/-! A genuine diffeomorphism has an invertible derivative in any fixed pair
of ordinary differentiable manifold charts. Tangent-space normalizations are
part of the constructed equivalence, rather than an identification premise. -/
public noncomputable section
namespace LeanShared.DiffeomorphismChartDerivative
open Set IsManifold
open scoped Manifold

theorem exists_equivalence
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (T : M ≃ₜ M) (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)))
    (hd : d.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)))
    (x : M) (inside : x ∈ c.source) (target : T x ∈ d.source) :
    ∃ L : E ≃L[ℝ] E, HasFDerivAt (d ∘ T ∘ c.symm) L.toContinuousLinearMap (c x) := by
  let C := hc.mfderiv inside
  let D := hd.mfderiv target
  let A := DiffeomorphismDifferential.differential T forward inverse x
  let L := (((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)).symm.trans C.symm).trans A).trans
    (D.trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (T x))))
  have source : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) c.symm (c x) C.symm.toContinuousLinearMap :=
    (hc.mdifferentiableAt_symm (c.map_source inside)).hasMFDerivAt
  have middle : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) T (c.symm (c x)) A.toContinuousLinearMap := by
    rw [c.left_inv inside]
    exact (forward x).hasMFDerivAt
  have last : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) d (T (c.symm (c x))) D.toContinuousLinearMap := by
    rw [c.left_inv inside]
    exact (hd.mdifferentiableAt target).hasMFDerivAt
  have raw := (last.comp (c x) (middle.comp (c x) source)).hasFDerivAt
  refine ⟨L,?_⟩
  exact raw

end LeanShared.DiffeomorphismChartDerivative
