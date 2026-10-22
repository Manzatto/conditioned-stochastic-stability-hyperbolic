module
public import LeanShared.Dynamics.HyperbolicChartOrbitUniqueness
public import LeanShared.Dynamics.LocalHyperbolicFiniteWindowDecay

/-! Exponential finite-window matching in actual coherent manifold coordinates.
The ambient metric is used only to choose one neighborhood; the quantitative
estimate is in actual hyperbolic coordinates, so an arbitrary compatible
ambient metric is not assumed to be locally Lipschitz. -/
public noncomputable section
namespace LeanShared.HyperbolicChartOrbitUniqueness
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem exists_finite_window_decay
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
      (∀ j, advance preserves (reference (j + 1)) = reference j) →
      ∀ (orbit : ℤ → M) (n : ℕ),
      (∀ j : ℕ, j < n → H (orbit (j + 1)) = orbit j) →
      (∀ j : ℕ, j ≤ n → dist (reference j).val (orbit j) < η) →
      ∀ j : ℕ, j ≤ n →
        ‖coordinate d frame (reference j) (orbit j)‖ ≤
          ((k + δ * 2 : ℝ≥0) : ℝ) ^ min j (n - j) * (2 * d.radius) := by
  obtain ⟨η, positiveη, nearby⟩ := exists_ambient_radius d frame positiveB inverse d.radius d.positive
  refine ⟨η, positiveη, fun reference referenceStep orbit n orbitStep close => ?_⟩
  let z := fun j => coordinate d frame (reference j) (orbit j)
  let maps := fun j => localMap d frame preserves (reference (j + 1))
  have bounded : ∀ j : ℕ, j ≤ n → ‖z j‖ ≤ d.radius :=
    fun j hj => (nearby _ _ (close j hj)).2.le
  have differentiable (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.radius) :
      DifferentiableAt ℝ (maps j) w :=
    (localMap_estimates d frame preserves forward inverse (reference (j + 1)) w hw).1
  have derivative (j : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.radius) :
      ‖fderiv ℝ (maps j) w -
        (A (reference (j + 1))).toContinuousLinearMap.prodMap (C (reference (j + 1)))‖ ≤ (δ : ℝ) := by
    have estimate := (localMap_estimates d frame preserves forward inverse
      (reference (j + 1)) w hw).2
    rw [linearization] at estimate
    exact estimate.le
  have zero : ∀ j, maps j 0 = 0 := fun j => localMap_zero d frame preserves _
  have step : ∀ j : ℕ, j < n → maps j (z (j + 1)) = z j := by
    intro j hj
    have actual := localMap_step d frame preserves (reference (j + 1)) (orbit (j + 1))
      (nearby _ _ (close (j + 1) (by omega))).1
    rw [referenceStep j, orbitStep j hj] at actual
    exact actual
  have estimate := LocalHyperbolicShadowing.finite_window_distance maps
    (fun j => A (reference (j + 1))) (fun j => C (reference (j + 1)))
    k δ small (fun j => expansion _) (fun j => contraction _)
    d.radius d.positive differentiable derivative zero z (fun _ => 0) n
    bounded (fun _ _ => by simpa only [norm_zero] using d.positive.le)
    step (fun j _ => zero j)
  intro j hj
  simpa only [dist_zero_right] using estimate j hj

end LeanShared.HyperbolicChartOrbitUniqueness
