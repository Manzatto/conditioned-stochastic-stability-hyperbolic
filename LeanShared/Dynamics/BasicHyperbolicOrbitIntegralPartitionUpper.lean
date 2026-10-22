module
public import LeanShared.Dynamics.BasicHyperbolicShadowedIntegralUpper
public import LeanShared.Dynamics.BasicHyperbolicSurvivorShadowing
public import LeanShared.Dynamics.WeightedOrbitSurvivorIntegral
public import LeanShared.Geometry.FiniteSmoothReferenceMapDomination

/-! A literal global orbit-product integral is bounded by the actual core
partition sum after fixed transient ends. No collar-pressure premise is used. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory ThermodynamicDefinitions
open scoped Manifold ContDiff NNReal ENNReal BigOperators

theorem BasicData.exists_orbit_integral_partition_upper
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
    (nonnegative : ∀ x, 0 ≤ g x) (supported : Function.support g ⊆ closure V)
    (γ : ℝ) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ∃ N : ℕ, 0 < N ∧ ∃ L : ℕ, 0 < L ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ p : ℕ, 0 < p →
        (∫⁻ y, ENNReal.ofReal (∏ j ∈ Finset.range (N*p+2*L+1), g ((T : M → M)^[j] y))
          ∂(referenceMeasure.measure μ)) ≤
        C * ENNReal.ofReal (γ^p) * ENNReal.ofReal (Real.exp (ε*(N*p))) *
          separatedPartitionSum T (b.hyperbolic.potential g) Λ (N*p+1) η := by
  obtain ⟨N, positiveN, C₀, finiteC₀, η, positiveη, upper⟩ :=
    b.exists_shadowed_integral_upper forward inverse g continuous positive γ hγ ε hε referenceMeasure μ
  obtain ⟨L, positiveL, shadow⟩ := b.survivor_shadowing forward
    (inverse.mdifferentiable (by norm_num)) η positiveη
  have forwardL : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (T^L : M ≃ₜ M) := by
    rw [DiffeomorphismIterates.coe_pow]
    exact forward.iterate L
  have inverseL : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 ((T^L).symm : M ≃ₜ M) := by
    rw [DiffeomorphismIterates.coe_symm_pow]
    exact inverse.iterate L
  obtain ⟨C₁, finiteC₁, mapBound⟩ := referenceMeasure.exists_map_domination μ (T^L) forwardL inverseL
  obtain ⟨B, bound⟩ := isCompact_univ.exists_bound_of_continuousOn continuous.continuousOn
  let G := max 1 B
  have positiveG : 0 ≤ G := zero_le_one.trans (le_max_left _ _)
  have bounded (x : M) : g x ≤ G := by
    have absolute : |g x| ≤ B := by simpa only [Real.norm_eq_abs] using bound x (mem_univ x)
    exact (le_abs_self _).trans (absolute.trans (le_max_right 1 B))
  let A := ENNReal.ofReal (G^(2*L+1)) * C₁
  have finiteA : A ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top finiteC₁
  refine ⟨N, positiveN, L, positiveL, A*C₀, ENNReal.mul_ne_top finiteA finiteC₀,
    η, positiveη, fun p hp => ?_⟩
  let S := (T^L) '' WeightedOrbitSurvivorIntegral.survivors T (closure V) (N*p+2*L)
  have shadowed : ∀ y ∈ S, ∃ x : Λ, ∀ j ≤ N*p,
      dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η := by
    rintro y ⟨z, survives, rfl⟩
    obtain ⟨x, traces⟩ := shadow (N*p) z survives
    refine ⟨x, fun j hj => ?_⟩
    have close := traces j hj
    simpa only [DiffeomorphismIterates.coe_pow, ← Function.iterate_add_apply,
      Nat.add_comm j L, dist_comm] using close
  have reduced := WeightedOrbitSurvivorIntegral.integral_bound T (referenceMeasure.measure μ)
    g continuous nonnegative G positiveG bounded (closure V) isClosed_closure supported
    L (N*p) C₁ mapBound
  calc
    _ ≤ A * ∫⁻ y in S,
        ENNReal.ofReal (∏ j ∈ Finset.range (N*p), g ((T : M → M)^[j] y))
        ∂(referenceMeasure.measure μ) := reduced
    _ ≤ A * (C₀ * ENNReal.ofReal (γ^p) * ENNReal.ofReal (Real.exp (ε*(N*p))) *
        separatedPartitionSum T (b.hyperbolic.potential g) Λ (N*p+1) η) :=
      mul_le_mul le_rfl (upper p hp S shadowed) bot_le bot_le
    _ = _ := by ac_rfl

end LeanShared.HyperbolicBasicSet
