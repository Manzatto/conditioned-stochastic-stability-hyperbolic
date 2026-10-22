module

public import LeanShared.Dynamics.BasicHyperbolicMainPeriodicPartitionError
public import LeanShared.Dynamics.BasicHyperbolicPeriodicPressure
public import LeanShared.Dynamics.BasicHyperbolicPeriodicPositivity
public import LeanShared.Dynamics.ActualBilateralPeriodicAsymptotic
public import LeanShared.Dynamics.MixingInvariantCore
public import LeanShared.Analysis.LeadingExponentialIdentification

/-! The actual BasicData periodic partition sums have leading exp(nP)
with a strictly smaller exponential relative error.  The Ruelle leading
eigenvalue is identified with ORIGINAL ambient pressure through actual
periodic counting and the already proved original pressure limit.
Neither symbolic pressure invariance nor a zeta source is assumed.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory Filter Function
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction Topology
open ThermodynamicDefinitions BilateralShadowingCoding MarkovFinitePathRealization FiniteClosedRefinement

set_option maxHeartbeats 1800000 in
theorem BasicData.periodic_asymptotic_of_actual_coding
    {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [TopologicalSpace J] [Fintype J]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    (rectangles : J → Set Λ)
    (code : Path (Transition (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles) → Λ)
    (properties : MarkovCodingProperties (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles code)
    (variation : HasExponentialVariations (fun a => ψ (code a).val)) :
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∃ τ D : ℝ,
      0 < τ ∧ τ < 1 ∧ 0 < D ∧ ∀ n : ℕ,
        |((Real.exp P) ^ (n + 1))⁻¹ * b.periodicPartitionSum forward inverse ψ (n + 1) - 1| ≤ D * τ ^ (n + 1) := by
  classical
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  obtain ⟨d, C, closed, statuses, law⟩ := properties.classifierOrigin
  let main := reindexedInteriorCode S C rectangles statuses law code
  have geometry := reindexedInteriorCode_finiteGeometry S C rectangles statuses law closed code properties
  obtain ⟨path, _coded⟩ := geometry.onto (Classical.arbitrary Λ)
  let : Nonempty (FuturePath (Transition S (interiorRectangles C))) := ⟨futureRestriction path⟩
  let φ : C(Path (Transition S (interiorRectangles C)), ℝ) :=
    ⟨fun a => ψ (main a).val,
      regular.differentiable.continuous.comp (continuous_subtype_val.comp geometry.continuous)⟩
  have variationφ : HasExponentialVariations φ :=
    interiorReindexPath_exponential S C rectangles statuses law (fun a => ψ (code a).val) variation
  obtain ⟨N, allConnections⟩ := mixing_interior_graph_common_connections S C closed
    (mixing.invariantCore b.hyperbolic.invariant)
  have connections := allConnections N le_rfl
  have nextConnections := allConnections (N + 1) (by omega)
  obtain ⟨positiveρ, κ, Cₐ, positiveκ, smallκ, positiveA, normalized⟩ :=
    actual_bilateral_periodic_relative_asymptotic φ variationφ N connections nextConnections
  let ρ := (abelRadiusReal (bilateralRuelleFuturePotential φ variationφ))⁻¹
  obtain ⟨P, pressureP, β, Cᵦ, positiveβ, smallβ, positiveB, comparison⟩ :=
    b.main_periodic_partition_exponential_error forward inverse mixing ψ α positiveα smallα regular
      C closed rectangles statuses law code properties
  obtain ⟨Q, pressureQ, originalGrowth⟩ := b.periodic_pressure_limit forward inverse mixing ψ α positiveα smallα regular
  have samePressure : P = Q := EReal.coe_injective (pressureP.symm.trans pressureQ)
  subst Q
  have shiftedGrowth : Tendsto (fun n => Real.log (b.periodicPartitionSum forward inverse ψ (n + 1)) /
      ((n + 1 : ℕ) : ℝ)) atTop (𝓝 P) := (tendsto_add_atTop_iff_nat 1).mpr originalGrowth
  obtain ⟨L, positiveFrom⟩ := eventually_atTop.mp (b.eventually_periodic_partition_positive forward inverse mixing ψ)
  have shiftedPositive : ∀ᶠ n : ℕ in atTop, 0 < b.periodicPartitionSum forward inverse ψ (n + 1) := by
    filter_upwards [eventually_ge_atTop L] with n hn
    exact positiveFrom (n + 1) (by omega)
  have leading : ρ = Real.exp P := LeadingExponentialIdentification.eq_exp
    (fun n => bilateralPeriodicWeightSum φ (n + 1))
    (fun n => b.periodicPartitionSum forward inverse ψ (n + 1)) P ρ κ Cₐ β Cᵦ
    positiveρ positiveκ smallκ positiveA.le positiveβ smallβ positiveB.le
    normalized comparison shiftedPositive shiftedGrowth
  let τ := max κ (β / Real.exp P)
  have positiveτ : 0 < τ := positiveκ.trans_le (le_max_left _ _)
  have smallRatio : β / Real.exp P < 1 := (div_lt_one (Real.exp_pos P)).mpr smallβ
  have smallτ : τ < 1 := max_lt smallκ smallRatio
  refine ⟨P, pressureP, τ, Cₐ + Cᵦ, positiveτ, smallτ, by positivity, ?_⟩
  intro n
  have normalizedA := normalized n
  change |(ρ ^ (n + 1))⁻¹ * bilateralPeriodicWeightSum φ (n + 1) - 1| ≤ Cₐ * κ ^ (n + 1) at normalizedA
  rw [leading] at normalizedA
  have difference := comparison n
  rw [abs_sub_comm] at difference
  have normalizedDifference : |((Real.exp P) ^ (n + 1))⁻¹ *
      (b.periodicPartitionSum forward inverse ψ (n + 1) - bilateralPeriodicWeightSum φ (n + 1))| ≤
      Cᵦ * (β / Real.exp P) ^ (n + 1) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    apply (mul_le_mul_of_nonneg_left difference (by positivity)).trans_eq
    rw [div_pow]
    ring
  have identity : ((Real.exp P) ^ (n + 1))⁻¹ * b.periodicPartitionSum forward inverse ψ (n + 1) - 1 =
      (((Real.exp P) ^ (n + 1))⁻¹ * bilateralPeriodicWeightSum φ (n + 1) - 1) +
        ((Real.exp P) ^ (n + 1))⁻¹ *
          (b.periodicPartitionSum forward inverse ψ (n + 1) - bilateralPeriodicWeightSum φ (n + 1)) := by ring
  rw [identity]
  apply ((abs_add_le _ _).trans (add_le_add normalizedA normalizedDifference)).trans
  calc
    _ ≤ Cₐ * τ ^ (n + 1) + Cᵦ * τ ^ (n + 1) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positiveκ.le (le_max_left _ _) _) positiveA.le)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) positiveB.le)
    _ = _ := by ring

end LeanShared.HyperbolicBasicSet
