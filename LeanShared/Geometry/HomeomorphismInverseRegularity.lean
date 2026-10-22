module
public import LeanShared.Geometry.ManifoldLocalInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A genuine manifold homeomorphism with C1 forward action and bijective
actual differential has a C1 inverse. The inverse regularity follows from
the ordinary inverse function theorem in actual charts. -/
public noncomputable section
namespace LeanShared.HomeomorphismInverseRegularity
open Set IsManifold
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1600000 in
theorem contMDiffAt_symm
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (H : M ≃ₜ M) (x : M) (smooth : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H x)
    (bijective : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)) :
    ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm (H x) := by
  exact LeanShared.ManifoldLocalInverse.contMDiffAt_of_eventually_leftInverse smooth bijective
    (Filter.Eventually.of_forall (fun z => H.symm_apply_apply z))

end LeanShared.HomeomorphismInverseRegularity
