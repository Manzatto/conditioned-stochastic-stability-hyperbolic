module
public import LeanShared.Dynamics.BasicHyperbolicRegularWeightedGluing
public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype
public import LeanShared.Dynamics.ProvedPressurePartitionEnvelope

/-! Actual mixing hyperbolic basic data and actual fractional potential
regularity construct TWO-SIDED uniform separated-partition normalization at the
literal ambient pressure. No expansivity, specification, Bowen, pressure,
Gibbs or partition-growth source is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction
open FiniteOrbitWordAssembly ThermodynamicDefinitions

set_option maxHeartbeats 2000000 in
theorem BasicData.eventual_partition_exponential_upper
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (continuous : Continuous ψ) :
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∀ ε > 0, ∀ η > 0,
      ∀ᶠ n : ℕ in Filter.atTop, separatedPartitionSum T ψ Λ (n + 1) ε ≤
        ENNReal.ofReal (Real.exp (((n + 1 : ℕ) : ℝ) * (P + η))) := by
  classical
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp b.hyperbolic.compact
  let : Nonempty Λ := b.nonempty.to_subtype
  let : MeasurableSpace Λ := borel Λ
  let : BorelSpace Λ := ⟨rfl⟩
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  have backwardS (x : Λ) : (S.symm x).val = T.symm x.val := rfl
  let φ : Λ →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ψ x.val, continuous.comp continuous_subtype_val⟩
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  have expansiveS : ∀ x y : Λ, (∀ j : ℕ,
      dist ((S : Λ → Λ)^[j] x) ((S : Λ → Λ)^[j] y) ≤ c ∧
      dist ((S.symm : Λ → Λ)^[j] x) ((S.symm : Λ → Λ)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have small := close j
    change dist (((S : Λ → Λ)^[j] x).val) (((S : Λ → Λ)^[j] y).val) ≤ c ∧
      dist (((S.symm : Λ → Λ)^[j] x).val) (((S.symm : Λ → Λ)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forwardS, iterate_coe_restriction S.symm backwardS] using small
  obtain ⟨P, pressureP⟩ := finite_pressure_of_expansive S c positiveC expansiveS φ φ.continuous
  have maximal (ν : MeasureTheory.ProbabilityMeasure Λ)
      (invariant : MeasureTheory.MeasurePreserving S (ν : MeasureTheory.Measure Λ) (ν : MeasureTheory.Measure Λ)) :
      (entropy S (ν : MeasureTheory.Measure Λ)).toReal + ∫ x, φ x ∂(ν : MeasureTheory.Measure Λ) ≤ P := by
    have lower := entropy_free_energy_le_pressure S c positiveC expansiveS ν invariant φ
    obtain ⟨H, entropyH⟩ := entropy_finite_of_expansive S c positiveC expansiveS ν invariant
    rw [entropyH, ← EReal.coe_add, pressureP] at lower
    simpa only [entropyH, EReal.toReal_coe] using EReal.coe_le_coe_iff.mp lower
  refine ⟨P, ?_, fun ε positiveε η positiveη => ?_⟩
  · rw [← pressure_restriction S forwardS ψ]
    exact pressureP
  · have upper := eventual_partition_growth S c positiveC expansiveS φ P maximal ε η positiveε positiveη
    filter_upwards [upper] with n bound
    change separatedPartitionSum S (fun z : Λ => ψ z.val) univ (n + 1) ε ≤ _ at bound
    simpa only [separatedPartitionSum_restriction S forwardS ψ, Nat.cast_add, Nat.cast_one] using bound

end LeanShared.HyperbolicBasicSet
