module
public import LeanShared.Dynamics.HyperbolicChartBowenDistortion
public import LeanShared.Geometry.CoherentFractionalObservable

/-! Actual fractional manifold regularity implies uniform finite-window
Bowen distortion in the constructed nonlinear hyperbolic coordinates.
No Hölder observable constant or Bowen estimate is a source premise. -/
public noncomputable section
namespace LeanShared.HyperbolicChartOrbitUniqueness
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem fractional_energy_distortion
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
      (A x).toContinuousLinearMap.prodMap (C x))
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ η > 0, ∃ D ≥ 0, ∀ (reference : ℤ → K),
      (∀ j, advance preserves (reference (j + 1)) = reference j) →
      ∀ (orbit : ℤ → M) (n : ℕ),
      (∀ j : ℕ, j < n → H (orbit (j + 1)) = orbit j) →
      (∀ j : ℕ, j ≤ n → dist (reference j).val (orbit j) < η) →
      |(∑ j ∈ Finset.range (n + 1), ψ (orbit j)) -
        (∑ j ∈ Finset.range (n + 1), ψ (reference j).val)| ≤ D := by
  obtain ⟨r, positiveR, L, nonnegativeL, holder⟩ :=
    exists_holder_increment d frame positiveB forward ψ α positiveα smallα regular
  let d' : CompactCoherentCenteredCharts.Data (E := E) (P := U × S) (Q := U × S)
      H K B (δ : ℝ) := {
    d with
    radius := min d.radius r
    positive := lt_min d.positive positiveR
    estimates := fun i hi j hj x hx hy e f he hf z hz =>
      d.estimates i hi j hj x hx hy e f he hf z (hz.trans (min_le_left _ _))
  }
  have same (x : K) (v : U × S) : decode d' frame x v = decode d frame x v := by
    unfold decode linear chart index
    rfl
  have holder' (x : K) (v : U × S) (hv : ‖v‖ ≤ d'.radius) :
      |ψ (decode d' frame x v) - ψ x.val| ≤ L * ‖v‖ ^ α := by
    rw [same]
    simpa only [Real.norm_eq_abs] using holder x v (hv.trans (min_le_right _ _))
  obtain ⟨η, positiveη, bound⟩ := exists_energy_distortion k δ d' frame preserves positiveB
    forward inverse A C small expansion contraction linearization
    ψ L α nonnegativeL positiveα holder'
  refine ⟨η, positiveη, _, ?_, bound⟩
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) nonnegativeL)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) d'.positive.le) _)
  · exact (sub_pos.mpr (Real.rpow_lt_one (NNReal.coe_nonneg _) small positiveα)).le

end LeanShared.HyperbolicChartOrbitUniqueness
