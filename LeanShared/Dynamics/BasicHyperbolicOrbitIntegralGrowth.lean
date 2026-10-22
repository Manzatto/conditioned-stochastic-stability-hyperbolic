module

public import LeanShared.Dynamics.BasicHyperbolicOrbitIntegralPartitionUpper
public import LeanShared.Dynamics.BasicHyperbolicCorePartitionUpper
public import LeanShared.Analysis.BoundedWeightedOrbitIntegrals
public import LeanShared.Analysis.PaddedGeometricGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Finiteness

/-! The literal positive orbit integrals have an all-length upper bound at
every rate strictly above the actual basic-set pressure. The geometric
producer, the core partition bound, padding and initial lengths are all
discharged here. Neither mixing nor a collar pressure is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory ThermodynamicDefinitions Filter
open scoped Manifold ContDiff BigOperators ENNReal Topology

set_option maxHeartbeats 3200000 in
theorem BasicData.exists_orbit_integral_growth
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
    (reference : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
      ∀ R : ℝ, Real.exp P < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x))
          ∂(reference.measure μ)) ≤ ENNReal.ofReal (C * R ^ n) := by
  classical
  have potentialContinuous := b.hyperbolic.continuousOn_potential forward
    (inverse.mdifferentiable one_ne_zero) g continuous.continuousOn positive
  obtain ⟨P, pressureP, partition⟩ := b.eventual_core_partition_exponential_upper
    forward inverse (b.hyperbolic.potential g) potentialContinuous
  refine ⟨P, pressureP, fun R above => ?_⟩
  have positiveR : 0 < R := (Real.exp_pos P).trans above
  let δ := (Real.log R - P) / 4
  have positiveδ : 0 < δ := by
    have below : P < Real.log R := (Real.lt_log_iff_exp_lt positiveR).mpr above
    dsimp only [δ]
    linarith
  obtain ⟨N, positiveN, L, _positiveL, C₀, finiteC₀, η, positiveη, padded⟩ :=
    b.exists_orbit_integral_partition_upper forward inverse g continuous positive nonnegative
      supported (Real.exp δ) (by simpa using (Real.exp_lt_exp.mpr positiveδ))
      δ positiveδ reference μ
  obtain ⟨n₀, partitionUpper⟩ := eventually_atTop.mp (partition η positiveη δ positiveδ)
  let σ := reference.measure μ
  let F := BoundedWeightedOrbitIntegrals.integral σ (T : M → M) g
  have Fnonnegative : ∀ n, 0 ≤ F n :=
    BoundedWeightedOrbitIntegrals.integral_nonnegative σ T g nonnegative
  have actualIntegral (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x)) ∂σ) =
        ENNReal.ofReal (F n) :=
    BoundedWeightedOrbitIntegrals.lintegral_eq σ T T.continuous g continuous nonnegative n
  have progression (p : ℕ) (largeP : n₀ + 1 ≤ p) :
      F (N * p + (2 * L + 1)) ≤
        (C₀.toReal * Real.exp (P + δ)) * R ^ (N * p) := by
    have positiveP : 0 < p := by omega
    have p_le : p ≤ N * p := Nat.le_mul_of_pos_left p positiveN
    have largeLength : n₀ ≤ N * p := by omega
    have boundPartition := partitionUpper (N * p) largeLength
    have bound := (padded p positiveP).trans
      (mul_le_mul le_rfl boundPartition bot_le bot_le)
    have realBound := ENNReal.toReal_mono (by finiteness) bound
    rw [actualIntegral] at realBound
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Fnonnegative _),
      ENNReal.toReal_ofReal (pow_nonneg (Real.exp_pos δ).le p),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at realBound
    have exponentBound :
        (Real.exp δ) ^ p * Real.exp (δ * (N * p : ℕ)) *
            Real.exp (((N * p + 1 : ℕ) : ℝ) * (P + δ)) ≤
          Real.exp (P + δ) * R ^ (N * p) := by
      have power : R ^ (N * p) = Real.exp (((N * p : ℕ) : ℝ) * Real.log R) := by
        rw [Real.exp_nat_mul, Real.exp_log positiveR]
      rw [← Real.exp_nat_mul, power, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have p_le_real : (p : ℝ) ≤ (N * p : ℕ) := by exact_mod_cast p_le
      have lengthNonnegative : 0 ≤ ((N * p : ℕ) : ℝ) := Nat.cast_nonneg _
      have scaledP := mul_le_mul_of_nonneg_right p_le_real positiveδ.le
      have scaledLength := mul_nonneg lengthNonnegative positiveδ.le
      have logarithm : Real.log R = P + 4 * δ := by dsimp only [δ]; ring
      simp only [Nat.cast_add, Nat.cast_one]
      rw [logarithm]
      nlinarith
    calc
      F (N * p + (2 * L + 1)) ≤ C₀.toReal * (Real.exp δ) ^ p *
          Real.exp (δ * (N * p : ℕ)) * Real.exp (((N * p + 1 : ℕ) : ℝ) * (P + δ)) := by
        simpa only [Nat.add_assoc, Nat.cast_mul] using realBound
      _ = C₀.toReal * ((Real.exp δ) ^ p * Real.exp (δ * (N * p : ℕ)) *
          Real.exp (((N * p + 1 : ℕ) : ℝ) * (P + δ))) := by ring
      _ ≤ C₀.toReal * (Real.exp (P + δ) * R ^ (N * p)) :=
        mul_le_mul_of_nonneg_left exponentBound ENNReal.toReal_nonneg
      _ = (C₀.toReal * Real.exp (P + δ)) * R ^ (N * p) := by ring
  obtain ⟨B, bounded⟩ := isCompact_univ.exists_bound_of_continuousOn continuous.continuousOn
  let G := max 1 B
  have nonnegativeG : 0 ≤ G := zero_le_one.trans (le_max_left _ _)
  have boundedG (x : M) : g x ≤ G := by
    have normBound : |g x| ≤ B := by
      simpa only [Real.norm_eq_abs] using bounded x (mem_univ x)
    exact (le_abs_self _).trans (normBound.trans (le_max_right _ _))
  obtain ⟨C, nonnegativeC, allLengths⟩ := PaddedGeometricGrowth.exists_all_length_bound
    F Fnonnegative R G positiveR nonnegativeG
    (BoundedWeightedOrbitIntegrals.integral_append_le σ T T.continuous g continuous
      nonnegative G nonnegativeG boundedG)
    N (2 * L + 1) (n₀ + 1) positiveN (C₀.toReal * Real.exp (P + δ))
    (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) progression
  refine ⟨C, nonnegativeC, fun n => ?_⟩
  rw [actualIntegral]
  exact ENNReal.ofReal_le_ofReal (allLengths n)

/-- The pressure witness is identified with the caller's actual pressure,
so this producer directly fills geometric coefficient-growth consumers. -/
theorem BasicData.orbit_integral_growth_at_pressure
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
    (reference : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (P : ℝ) (pressureP : pressure T (b.hyperbolic.potential g) Λ = (P : EReal))
    (R : ℝ) (above : Real.exp P < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] x))
        ∂(reference.measure μ)) ≤ ENNReal.ofReal (C * R ^ n) := by
  obtain ⟨P', identity, bound⟩ := b.exists_orbit_integral_growth forward inverse
    g continuous positive nonnegative supported reference μ
  have same : P' = P := EReal.coe_injective (identity.symm.trans pressureP)
  subst P'
  exact bound R above

end LeanShared.HyperbolicBasicSet
