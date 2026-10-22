module
public import LeanShared.Dynamics.HyperbolicCoherentNonlinearCharts
public import LeanShared.Dynamics.HyperbolicChartFiniteWindowDecay
public import Mathlib.Tactic.NormNum

/-! Exponential finite-window coordinate matching from literal compact
hyperbolic basic data. All dimensions, frames, iterates, charts and radii
are constructed internally; the contraction factor is the fixed 3/8. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_finite_window_coordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm) :
    ∃ a : IsometricFraming b.hyperbolic, ∃ N : ℕ, 0 < N ∧
      ∃ B : ℝ, ∃ d : CompactCoherentCenteredCharts.Data (E := E)
        (P := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        (Q := EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
        ((T ^ N : M ≃ₜ M) : M → M) Λ B (1 / 16),
      ∃ η > 0, ∀ reference : ℤ → Λ,
      (∀ j, (T ^ N) (reference (j + 1)).val = (reference j).val) →
      ∀ (orbit : ℤ → M) (n : ℕ),
      (∀ j : ℕ, j < n → (T ^ N) (orbit (j + 1)) = orbit j) →
      (∀ j : ℕ, j ≤ n → dist (reference j).val (orbit j) < η) →
      ∀ j : ℕ, j ≤ n →
        ‖coordinate d a.whole (reference j) (orbit j)‖ ≤
          (3 / 8 : ℝ) ^ min j (n - j) * (2 * d.radius) := by
  obtain ⟨a, N, positiveN, B, positiveB, frameBounds, ⟨d⟩, blocks⟩ :=
    b.exists_coherent_nonlinear_charts forward inverse (1 / 4) (1 / 16) (by norm_num) (by norm_num)
  let k : ℝ≥0 := ⟨1 / 4, by norm_num⟩
  let δ : ℝ≥0 := ⟨1 / 16, by norm_num⟩
  let H := ((T^N : M ≃ₜ M) : M → M)
  have preserves : MapsTo H Λ Λ := by
    have step : MapsTo T Λ Λ := fun x hx => by
      rw [← b.hyperbolic.invariant]
      exact mem_image_of_mem T hx
    intro x hx
    change ((T^N : M ≃ₜ M) : M → M) x ∈ Λ
    rw [DiffeomorphismIterates.coe_pow]
    exact step.iterate N hx
  choose S U boundS boundU actual using blocks
  have linearization (x : Λ) :
      (a.whole (advance preserves x)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
      (U x).toContinuousLinearMap.prodMap (S x).toContinuousLinearMap := by
    have same : advance preserves x = b.hyperbolic.iteratePoint N x := Subtype.ext rfl
    apply ContinuousLinearMap.ext
    intro z
    change (a.whole (advance preserves x)).symm
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val (a.whole x z)) = (U x z.1, S x z.2)
    rw [same]
    exact actual x z
  obtain ⟨η, positiveη, decay⟩ := HyperbolicChartOrbitUniqueness.exists_finite_window_decay
    k δ d a.whole preserves positiveB (fun x => (frameBounds x).1) (fun x => (frameBounds x).2)
    U (fun x => (S x).toContinuousLinearMap) (by change (1 / 4 : ℝ) + (1 / 16) * 2 < 1; norm_num) boundU boundS linearization
  refine ⟨a, N, positiveN, B, d, η, positiveη, ?_⟩
  intro reference referenceStep orbit n orbitStep close j hj
  have estimate := decay reference (fun m => Subtype.ext (referenceStep m))
    orbit n orbitStep close j hj
  change ‖coordinate d a.whole (reference j) (orbit j)‖ ≤
    ((1 / 4 + 1 / 16 * 2 : ℝ≥0) : ℝ) ^ min j (n - j) * (2 * d.radius) at estimate
  norm_num only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, one_div, invOf_eq_inv, inv_mul_eq_div] at estimate
  exact estimate

end LeanShared.HyperbolicBasicSet
