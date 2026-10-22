module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedPairIdentification
meta import Lean.LibrarySuggestions.Basic

/-! The leading records of the analytic pair together with the consumer ratio. If every leading
record of the raw intermediate generator at rate `λ` has product value `value ψ` against the
multiplier `M ψ`, then the leading records of the pair have consumer ratio `value ψ` for every
`ψ`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelPairIdentification"

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

/-- The intermediate norm identity of a tower. -/
abbrev NormIdH : Prop := ∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖

/-- The weak norm identity of a tower. -/
abbrev NormIdW : Prop := ∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖

/-- The quantitative pair data of a tower. -/
abbrev PairData (hnormH : NormIdH m₀ m₁) (hnorm₁ : NormIdW m₁ m₂) :=
  ProducedAnnealedPair.QuantitativeData (towerInclusionH m₀ m₁ hnormH)
    (towerInclusion m₁ m₂ hnorm₁) law hprob (fun ε z => m₀.generator (G ε z))
    (fun ε z => m₁.generator (G ε z)) R ρ₀ ρ₁ weak₀ weak₁

/-- The identified pair: tower norm identities, quantitative pair data, and leading records of
both normalized zero-noise operators at rate `λ / R` whose consumer ratio against `multiplier ψ` is
`value ψ`. -/
def PairIdentifiedConclusion (lam : ℝ) {Ψ : Type*}
    (multiplier : Ψ → m₁.StrongSpace →L[ℂ] m₁.StrongSpace) (value : Ψ → ℝ) : Prop :=
  ∃ hnormH : NormIdH m₀ m₁, ∃ hnorm₁ : NormIdW m₁ m₂,
      ∃ q : PairData m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ hnormH hnorm₁,
      ∃ ds : DeterministicLeading (q.pair.strong.operator 0),
      ∃ dm : DeterministicLeading (q.pair.intermediate.operator 0),
        ds.rate = R⁻¹ * lam ∧ dm.rate = R⁻¹ * lam ∧
        ∀ ψ, (dm.mean (multiplier ψ (towerInclusionH m₀ m₁ hnormH ds.vector)) /
          dm.mean (towerInclusionH m₀ m₁ hnormH ds.vector)).re = value ψ

set_option maxHeartbeats 4000000 in
/-- The leading records of the pair with their consumer ratios. -/
theorem PairStatement.identified (h : PairStatement m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁)
    (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (lam : ℝ) (gap₀ : ρ₀ < lam) (gap₁ : ρ₁ < lam)
    (lead₀ : ∀ (i : m₀.StrongSpace →L[ℂ] m₂.StrongSpace), IsCompactOperator i →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖((m₀.generator a₀) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖i x‖) → α < lam →
      ∃ d : DeterministicLeading (m₀.generator a₀), d.rate = lam)
    (lead₁ : ∀ (i : m₁.StrongSpace →L[ℂ] m₂.StrongSpace), IsCompactOperator i →
      ∀ α R' C D : ℝ, 0 ≤ α → 0 ≤ R' → 0 ≤ C → 0 ≤ D →
      (∀ n x, ‖((m₁.generator a₀) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R' ^ n * ‖i x‖) → α < lam →
      ∃ d : DeterministicLeading (m₁.generator a₀), d.rate = lam)
    {Ψ : Type*} (multiplier : Ψ → m₁.StrongSpace →L[ℂ] m₁.StrongSpace) (value : Ψ → ℝ)
    (identified : ∀ ψ (d : DeterministicLeading (m₁.generator a₀)), d.rate = lam →
      (d.mean (multiplier ψ d.vector)).re = value ψ) :
    PairIdentifiedConclusion m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ lam multiplier value := by
  have hLeading :=
    PairStatement.leading m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ h a₀ G0 lam gap₀ gap₁ lead₀ lead₁
  rcases hLeading with ⟨hnormH, hnorm₁, q, ds, dm, hds, hdm⟩
  have hH : ∀ z, (fun ε z => m₁.generator (G ε z)) 0 z = m₁.generator a₀ := fun z =>
    congrArg m₁.generator (G0 z)
  unfold PairIdentifiedConclusion
  refine ⟨hnormH, hnorm₁, q, ds, dm, hds, hdm, fun ψ => ?_⟩
  refine q.identified_ratio (m₁.generator a₀) ?_ ds dm ?_ lam ?_ (multiplier ψ) (value ψ) ?_
  · exact hH
  · exact hds.trans hdm.symm
  · exact hdm
  · exact identified ψ

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
