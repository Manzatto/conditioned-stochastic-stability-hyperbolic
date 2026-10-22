module
public import LeanShared.Geometry.CoherentCenteredMapDynamics
public import LeanShared.Geometry.CoherentCenteredCoordinateBounds
public import LeanShared.Dynamics.LocalHyperbolicOrbitUniqueness

/-! Actual uniformly hyperbolic chart dynamics separate complete nearby
orbits. The ambient separation radius is derived from the finite chart cover;
local map equations and the bilateral contraction are derived internally. -/
public noncomputable section
namespace LeanShared.HyperbolicChartOrbitUniqueness
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem exists_separation_radius
    {E M U S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B : ℝ} (k δ : ℝ≥0)
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := U × S) (Q := U × S) H K B (δ : ℝ))
    (frame : ∀ x : K, (U × S) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (positiveB : 0 < B)
    (forward : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (inverse : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (A : K → U ≃L[ℝ] U) (C : K → S →L[ℝ] S)
    (small : k + δ * 2 < 1)
    (expansion : ∀ x, ‖(A x).symm.toContinuousLinearMap‖ ≤ (k : ℝ))
    (contraction : ∀ x, ‖C x‖ ≤ (k : ℝ))
    (linearization : ∀ x,
      (frame (advance preserves x)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap) =
      (A x).toContinuousLinearMap.prodMap (C x)) :
    ∃ η > 0, ∀ (reference : ℤ → K),
      (∀ n, advance preserves (reference (n + 1)) = reference n) →
      ∀ orbit : ℤ → M, (∀ n, H (orbit (n + 1)) = orbit n) →
      (∀ n, dist (reference n).val (orbit n) < η) → ∀ n, orbit n = (reference n).val := by
  obtain ⟨η, positiveη, nearby⟩ := exists_ambient_radius d frame positiveB inverse d.radius d.positive
  refine ⟨η, positiveη, fun reference referenceStep orbit orbitStep close => ?_⟩
  let z := fun n => coordinate d frame (reference n) (orbit n)
  let maps := fun n => localMap d frame preserves (reference (n + 1))
  have bounded : ∀ n, ‖z n‖ ≤ d.radius := fun n => (nearby _ _ (close n)).2.le
  have differentiable (n : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.radius) :
      DifferentiableAt ℝ (maps n) w :=
    (localMap_estimates d frame preserves forward inverse (reference (n + 1)) w hw).1
  have derivative (n : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.radius) :
      ‖fderiv ℝ (maps n) w -
        (A (reference (n + 1))).toContinuousLinearMap.prodMap (C (reference (n + 1)))‖ ≤ (δ : ℝ) := by
    have estimate := (localMap_estimates d frame preserves forward inverse
      (reference (n + 1)) w hw).2
    rw [linearization] at estimate
    exact estimate.le
  have zero : ∀ n, maps n 0 = 0 := fun n => localMap_zero d frame preserves _
  have step : ∀ n, maps n (z (n + 1)) = z n := by
    intro n
    have actual := localMap_step d frame preserves (reference (n + 1)) (orbit (n + 1))
      (nearby _ _ (close (n + 1))).1
    rw [referenceStep n, orbitStep n] at actual
    exact actual
  have zeroCoordinates := LocalHyperbolicOrbitUniqueness.eq_zero maps
    (fun n => A (reference (n + 1))) (fun n => C (reference (n + 1)))
    k δ small (fun n => expansion _) (fun n => contraction _)
    d.radius d.positive differentiable derivative zero z bounded step
  intro n
  have actual := decode_coordinate d frame (reference n) (orbit n) (nearby _ _ (close n)).1
  change decode d frame (reference n) (z n) = orbit n at actual
  rw [zeroCoordinates n, decode_zero] at actual
  exact actual.symm

end LeanShared.HyperbolicChartOrbitUniqueness
