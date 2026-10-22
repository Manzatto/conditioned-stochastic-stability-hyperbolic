module
public import LeanShared.Dynamics.HyperbolicChartFiniteWindowDecay
public import LeanShared.Dynamics.TwoSidedGeometricDistortion

/-! Actual nonlinear hyperbolic coordinates turn a local Hölder observable
estimate into a uniform Bowen energy bound. Coordinate decay is proved from
the derivative blocks, rather than supplied as an exponential orbit premise. -/
public noncomputable section
namespace LeanShared.HyperbolicChartOrbitUniqueness
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open LeanShared.CoherentCenteredCoordinateMaps

set_option maxHeartbeats 2400000 in
theorem exists_energy_distortion
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
    (ψ : M → ℝ) (L α : ℝ) (nonnegativeL : 0 ≤ L) (positiveα : 0 < α)
    (holder : ∀ x : K, ∀ v : U × S, ‖v‖ ≤ d.radius →
      |ψ (decode d frame x v) - ψ x.val| ≤ L * ‖v‖ ^ α) :
    ∃ η > 0, ∀ (reference : ℤ → K),
      (∀ j, advance preserves (reference (j + 1)) = reference j) →
      ∀ (orbit : ℤ → M) (n : ℕ),
      (∀ j : ℕ, j < n → H (orbit (j + 1)) = orbit j) →
      (∀ j : ℕ, j ≤ n → dist (reference j).val (orbit j) < η) →
      |(∑ j ∈ Finset.range (n + 1), ψ (orbit j)) -
        (∑ j ∈ Finset.range (n + 1), ψ (reference j).val)| ≤
        2 * L * (2 * d.radius) ^ α / (1 - ((k + δ * 2 : ℝ≥0) : ℝ) ^ α) := by
  obtain ⟨η₀, positive₀, nearby⟩ :=
    exists_ambient_radius d frame positiveB inverse d.radius d.positive
  obtain ⟨η₁, positive₁, decay⟩ := exists_finite_window_decay k δ d frame preserves
    positiveB forward inverse A C small expansion contraction linearization
  refine ⟨min η₀ η₁, lt_min positive₀ positive₁, ?_⟩
  intro reference referenceStep orbit n orbitStep close
  have close₀ (j : ℕ) (hj : j ≤ n) : dist (reference j).val (orbit j) < η₀ :=
    (close j hj).trans_le (min_le_left _ _)
  have close₁ (j : ℕ) (hj : j ≤ n) : dist (reference j).val (orbit j) < η₁ :=
    (close j hj).trans_le (min_le_right _ _)
  have normBound := decay reference referenceStep orbit n orbitStep close₁
  let q : ℝ := ((k + δ * 2 : ℝ≥0) : ℝ)
  have qnonnegative : 0 ≤ q := NNReal.coe_nonneg _
  have qsmall : q < 1 := small
  have powered (m : ℕ) : (q ^ m) ^ α = (q ^ α) ^ m := by
    rw [← Real.rpow_natCast_mul qnonnegative, mul_comm,
      Real.rpow_mul qnonnegative, Real.rpow_natCast]
  have radiusNonnegative : 0 ≤ 2 * d.radius := mul_nonneg (by norm_num) d.positive.le
  have terms (j : ℕ) (hj : j < n + 1) :
      |ψ (orbit j) - ψ (reference j).val| ≤
        (L * (2 * d.radius) ^ α) * (q ^ α) ^ min j (n + 1 - 1 - j) := by
    have jn : j ≤ n := by omega
    have localBound := holder (reference j)
      (coordinate d frame (reference j) (orbit j)) (nearby _ _ (close₀ j jn)).2.le
    rw [decode_coordinate d frame _ _ (nearby _ _ (close₀ j jn)).1] at localBound
    calc
      _ ≤ L * ‖coordinate d frame (reference j) (orbit j)‖ ^ α := localBound
      _ ≤ L * (q ^ min j (n - j) * (2 * d.radius)) ^ α :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (normBound j jn) positiveα.le) nonnegativeL
      _ = _ := by
        rw [Real.mul_rpow (pow_nonneg qnonnegative _) radiusNonnegative, powered]
        simp only [Nat.add_sub_cancel]
        ring
  have estimate := HolderBowenDistortion.sum_difference_bound
    (fun j : ℕ => ψ (orbit j)) (fun j : ℕ => ψ (reference j).val)
    (L * (2 * d.radius) ^ α) (q ^ α)
    (mul_nonneg nonnegativeL (Real.rpow_nonneg radiusNonnegative _))
    (Real.rpow_nonneg qnonnegative _) (Real.rpow_lt_one qnonnegative qsmall positiveα)
    (n + 1) terms
  convert estimate using 1; ring

end LeanShared.HyperbolicChartOrbitUniqueness
