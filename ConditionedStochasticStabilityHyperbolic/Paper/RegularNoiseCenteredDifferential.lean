module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFirstDerivative
public import LeanShared.Analysis.BoundedFramePerturbation
public import LeanShared.Geometry.DiffeomorphismDifferential
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Literal Whitney first-derivative closeness survives the constructed
centered linear coordinates, with the exact frame-norm factors. All coordinate
differentiability is derived from the actual manifold maps and chart domains. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold
open scoped Manifold ContDiff NNReal
open LeanShared.CenteredManifoldCoordinates

 theorem WhitneyAtlas.coordinate_differentiableAt
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    {T f : M → M} (A : WhitneyAtlas (E := E) T)
    (smooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) f)
    (target : ∀ i, f '' closure (A.patch i) ⊆ (A.target i).source)
    (i : Fin A.count) (y : E) (inside : y ∈ A.coordinatePatch i) :
    DifferentiableAt ℝ (A.coordinate f i) y := by
  have source := (contMDiffAt_symm_of_mem_maximalAtlas (A.source_smooth i)
    inside.1).mdifferentiableAt (by simp)
  have middle := (smooth ((A.source i).symm y)).comp y source
  have target_member : f ((A.source i).symm y) ∈ (A.target i).source :=
    target i (mem_image_of_mem f (subset_closure inside.2))
  have last := (contMDiffAt_of_mem_maximalAtlas (A.target_smooth i)
    target_member).mdifferentiableAt (by simp)
  exact (last.comp y middle).differentiableAt

 theorem Maps.centered_coordinate_fderiv_close
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (control : cube (ι := ι) ε) (i : Fin F.atlas.count)
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E) (a b : E) (z : P)
    (inside : a + L z ∈ F.atlas.coordinatePatch i) :
    ‖fderiv ℝ (centered L R a b (F.atlas.coordinate (F.family ε control.val) i)) z -
      fderiv ℝ (centered L R a b (F.atlas.coordinate T i)) z‖ ≤
      ‖R.symm.toContinuousLinearMap‖ *
        ((F.constant * (ε : ℝ)) * ‖L.toContinuousLinearMap‖) := by
  have noisy := F.atlas.coordinate_differentiableAt
    ((F.map_regular ε positive window control).mdifferentiable regularity)
    (F.whitney_bound ε positive window control).target_control i (a + L z) inside
  have reference := F.atlas.coordinate_differentiableAt deterministic
    F.atlas.deterministic_target i (a + L z) inside
  exact LeanShared.BoundedFramePerturbation.derivative_difference_le L R a b _ _ z
    noisy reference _ (F.coordinate_fderiv_close regularity ε positive window control
      i (a + L z) inside)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
