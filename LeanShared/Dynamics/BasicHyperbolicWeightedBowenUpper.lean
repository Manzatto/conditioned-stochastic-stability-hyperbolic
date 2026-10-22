module
public import LeanShared.Dynamics.BasicHyperbolicBowenVolumeUpper
public import LeanShared.Dynamics.CompactPositiveWeightUpperDistortion
public import LeanShared.Dynamics.HyperbolicOrbitWeightJacobian

/-! Actual weighted Bowen-ball integrals, with arbitrarily small weight
loss and the native unstable-Jacobian cancellation. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory ThermodynamicDefinitions
open scoped Manifold ContDiff NNReal ENNReal BigOperators

theorem BasicData.exists_weighted_bowen_integral_upper
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (g : M → ℝ) (continuous : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (γ : ℝ) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ p : ℕ, 0 < p → ∀ x : Λ,
        (∫⁻ y in {y | ∀ j ≤ N*p,
          dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η},
          ENNReal.ofReal (∏ j ∈ Finset.range (N*p), g ((T : M → M)^[j] y))
          ∂(referenceMeasure.measure μ)) ≤
        C * ENNReal.ofReal (γ^p) * ENNReal.ofReal (Real.exp (ε*(N*p))) *
          ENNReal.ofReal (Real.exp (orbitSum T (b.hyperbolic.potential g) (N*p) x.val)) := by
  obtain ⟨N, positiveN, C, finiteC, η, positiveη, volume⟩ :=
    b.exists_bowen_volume_upper forward inverse γ hγ referenceMeasure μ
  obtain ⟨ρ, positiveρ, distortion⟩ :=
    CompactPositiveWeightUpperDistortion.exists_orbit_radius Λ b.hyperbolic.compact
      g continuous positive ε hε
  let r := min η ρ
  refine ⟨N, positiveN, C, finiteC, r, lt_min positiveη positiveρ, fun p hp x => ?_⟩
  let n := N*p
  let W := {y | ∀ j ≤ n, dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < r}
  let J := ENNReal.ofReal (∏ j ∈ Finset.range n,
    b.hyperbolic.unstableJacobian ((T : M → M)^[j] x.val))
  let A := ENNReal.ofReal (Real.exp (ε*n)) *
    ENNReal.ofReal (Real.exp (orbitSum T (b.hyperbolic.potential g) n x.val))
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  have points (y : M) (hy : y ∈ W) :
      ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] y)) ≤ A*J := by
    have bound := (distortion n (fun j => (T : M → M)^[j] x.val)
      (fun j => (T : M → M)^[j] y)
      (fun j _ => invariant.iterate j x.property)
      (fun j hj => by simpa only [dist_comm] using (hy j (Nat.le_of_lt hj)).trans_le (min_le_right η ρ))).2
    have identity := b.hyperbolic.orbit_weight_eq_energy_jacobian
      (forward.mdifferentiable (by norm_num)) (inverse.mdifferentiable (by norm_num))
      g positive n x.val x.property
    rw [← identity] at bound
    have enn := ENNReal.ofReal_le_ofReal bound
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le] at enn
    simpa only [A, J, mul_assoc] using enn
  have volumeW : J * (referenceMeasure.measure μ) W ≤ C * ENNReal.ofReal (γ^p) := by
    apply le_trans (mul_le_mul le_rfl (measure_mono (show W ⊆ {y | ∀ j ≤ N*p,
      dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η} from
      fun y hy j hj => (hy j hj).trans_le (min_le_left η ρ))) bot_le bot_le)
    exact volume p hp x
  calc
    _ ≤ ∫⁻ _ in W, A*J ∂(referenceMeasure.measure μ) := setLIntegral_mono measurable_const points
    _ = A*(J*(referenceMeasure.measure μ) W) := by rw [setLIntegral_const, mul_assoc]
    _ ≤ A*(C*ENNReal.ofReal (γ^p)) := mul_le_mul le_rfl volumeW bot_le bot_le
    _ = _ := by dsimp [A,n]; simp only [Nat.cast_mul]; ac_rfl

end LeanShared.HyperbolicBasicSet
