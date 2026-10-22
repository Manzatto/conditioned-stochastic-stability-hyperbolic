module

public import LeanShared.Dynamics.BasicHyperbolicBowenCylinderVolume
public import LeanShared.Dynamics.CompactPositiveOrbitWeightDistortion
public import LeanShared.Dynamics.HyperbolicOrbitWeightJacobian
public import LeanShared.Dynamics.SeparatedTrackingCylinders
public import LeanShared.MeasureTheory.FiniteCylinderIntegralLower

/-! Actual positive matrix-coefficient lower bounds from genuine disjoint
manifold cylinders. Weight distortion, cylinder volume and unstable
Jacobian cancellation are constructed, not supplied as sources. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Bundle ENNReal BigOperators
open ThermodynamicDefinitions

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_weighted_cylinder_integral_lower
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (g : M → ℝ) (continuous : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (γ : ℝ) (hγ : 1 < γ) :
    ∃ N : ℕ, 0 < N ∧ ∀ ξ : ℝ, 0 < ξ → ∀ ρ : ℝ, 0 < ρ →
      ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∃ v : ℝ, 0 < v ∧
      ∀ p : ℕ, 0 < p → ∀ s : Finset M, Separated T Λ (N * p) ρ s →
        ENNReal.ofReal v * ENNReal.ofReal (Real.exp (-ξ * (N * p))) *
          (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T (b.hyperbolic.potential g) (N * p) x))) ≤
        C * ENNReal.ofReal (γ ^ p) *
          ∫⁻ y, ENNReal.ofReal (∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y))
            ∂(referenceMeasure.measure μ) := by
  classical
  obtain ⟨N, positiveN, cylinders⟩ := b.exists_bowen_cylinder_volume forward inverse γ hγ referenceMeasure μ
  refine ⟨N, positiveN, fun ξ positiveξ ρ positiveρ => ?_⟩
  obtain ⟨τ, positiveτ, weights⟩ := CompactPositiveOrbitWeightDistortion.exists_radius
    Λ b.hyperbolic.compact g continuous positive ξ positiveξ
  let ε := min (ρ / 3) (τ / 2)
  have positiveε : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨C, finiteC, v, positiveV, sets⟩ := cylinders ε positiveε
  refine ⟨C, finiteC, v, positiveV, fun p hp s separated => ?_⟩
  choose W openW tracking volumes using (fun x : Λ => sets p hp x)
  let family := fun x : M => if hx : x ∈ Λ then W ⟨x, hx⟩ else ∅
  have family_eq (x : M) (hx : x ∈ Λ) : family x = W ⟨x, hx⟩ := dite_eq_left hx
  have follows (x : M) (hx : x ∈ s) (y : M) (hy : y ∈ family x) (j : ℕ) (hj : j ≤ N * p) :
      dist ((T : M → M)^[j] y) ((T : M → M)^[j] x) < ε := by
    rw [family_eq x (separated.1 x hx)] at hy
    exact tracking ⟨x, separated.1 x hx⟩ y hy j hj
  have disjoint := SeparatedTrackingCylinders.pairwise_disjoint (T : M → M) Λ (N * p) ρ positiveρ
    s separated family (fun x hx y hy j hj => (follows x hx y hy j hj.le).trans_le (min_le_left _ _))
  let a := fun x => ENNReal.ofReal (Real.exp (-ξ * (N * p)) *
    Real.exp (orbitSum T (b.hyperbolic.potential g) (N * p) x))
  let J := fun x => ∏ j ∈ Finset.range (N * p), b.hyperbolic.unstableJacobian ((T : M → M)^[j] x)
  have volume (x : M) (hx : x ∈ s) : ENNReal.ofReal v ≤
      (C * ENNReal.ofReal (γ ^ p)) * ENNReal.ofReal (J x) * (referenceMeasure.measure μ) (family x) := by
    have bound := volumes ⟨x, separated.1 x hx⟩
    rw [← family_eq x (separated.1 x hx)] at bound
    simpa only [J, ENNReal.ofReal_mul (pow_nonneg (by linarith : 0 ≤ γ) p), mul_assoc] using bound
  have point (x : M) (hx : x ∈ s) (y : M) (hy : y ∈ family x) :
      a x * ENNReal.ofReal (J x) ≤
        ENNReal.ofReal (∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y)) := by
    have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
    have weight := (weights (N * p) (fun j => (T : M → M)^[j] x) (fun j => (T : M → M)^[j] y)
      (fun j _ => invariant.iterate j (separated.1 x hx)) (fun j hj => by
        rw [dist_comm]
        exact lt_of_lt_of_le (follows x hx y hy j hj.le)
          ((min_le_right _ _).trans (half_le_self positiveτ.le)))).2
    have identity := b.hyperbolic.orbit_weight_eq_energy_jacobian
      (forward.mdifferentiable one_ne_zero) (inverse.mdifferentiable one_ne_zero)
      g positive (N * p) x (separated.1 x hx)
    have lower : (Real.exp (-ξ * (N * p)) * Real.exp (orbitSum T (b.hyperbolic.potential g) (N * p) x)) *
        J x ≤ ∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y) := by
      rw [mul_assoc, identity]
      simpa only [Nat.cast_mul] using weight
    change ENNReal.ofReal _ * ENNReal.ofReal (J x) ≤ _
    rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal lower
  have result := FiniteCylinderIntegralLower.bound (referenceMeasure.measure μ) s family disjoint
    (fun x hx => by rw [family_eq x (separated.1 x hx)]; exact (openW _).measurableSet)
    (fun y => ENNReal.ofReal (∏ j ∈ Finset.range (N * p), g ((T : M → M)^[j] y)))
    (ENNReal.ofReal v) (C * ENNReal.ofReal (γ ^ p)) a (fun x => ENNReal.ofReal (J x)) volume point
  simpa only [a, ENNReal.ofReal_mul (Real.exp_pos _).le, ← Finset.mul_sum, ← mul_assoc] using result

end LeanShared.HyperbolicBasicSet
