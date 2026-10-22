module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedPairLeading
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading records of the analytic pair. The zero-noise generator of each strong
stage is the model generator of the reference letter; the records carry its raw compact two-norm
estimate with rate the principal rate, so a raw leading theorem for each stage gives leading
records of the normalized zero-noise operators at rate `λ / R`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelPairLeading"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter Topology IsManifold MeasureTheory
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelWeakTower
open PhysicalModelTowerFacts KellerLiverani1999 LeanShared.TwoNormNormalization

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m₀ m₁ m₂ : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε)) (G : ℝ≥0 → Z → Ω)
  (R ρ₀ ρ₁ weak₀ weak₁ : ℝ)

set_option maxHeartbeats 3200000 in
/-- A raw leading theorem for each strong stage gives the leading records of the pair. -/
theorem PairStatement.leading (h : PairStatement m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁)
    (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (lam : ℝ) (gap₀ : ρ₀ < lam) (gap₁ : ρ₁ < lam)
    (lead₀ : ∀ (i : m₀.StrongSpace →L[ℂ] m₂.StrongSpace), IsCompactOperator i →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖((m₀.generator a₀) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖i x‖) → α < lam →
      ∃ d : DeterministicLeading (m₀.generator a₀), d.rate = lam)
    (lead₁ : ∀ (i : m₁.StrongSpace →L[ℂ] m₂.StrongSpace), IsCompactOperator i →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖((m₁.generator a₀) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖i x‖) → α < lam →
      ∃ d : DeterministicLeading (m₁.generator a₀), d.rate = lam) :
    ∃ hnormH : (∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖), ∃ hnorm₁ : (∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖),
      ∃ q : ProducedAnnealedPair.QuantitativeData (towerInclusionH m₀ m₁ hnormH)
        (towerInclusion m₁ m₂ hnorm₁) law hprob (fun ε z => m₀.generator (G ε z))
        (fun ε z => m₁.generator (G ε z)) R ρ₀ ρ₁ weak₀ weak₁,
      ∃ ds : DeterministicLeading (q.pair.strong.operator 0),
      ∃ dm : DeterministicLeading (q.pair.intermediate.operator 0),
        ds.rate = R⁻¹ * lam ∧ dm.rate = R⁻¹ * lam := by
  obtain ⟨hnormH, hnorm₁, ⟨q⟩⟩ := h
  exact ⟨hnormH, hnorm₁, q, q.leading (m₀.generator a₀) (m₁.generator a₀)
    (fun z => congrArg m₀.generator (G0 z)) (fun z => congrArg m₁.generator (G0 z)) lam gap₀ gap₁
    lead₀ lead₁⟩

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
