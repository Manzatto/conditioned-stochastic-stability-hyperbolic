module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedPair
meta import Lean.LibrarySuggestions.Basic

/-! The pair statement of three physical stages from block words, for any normalizing scale
`scale ≥ 1` above the principal rate (rather than the fixed `max 1 (ρ + 1)`), so that the scale
can also dominate a prescribed weight bound. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelAnnealedPairScale"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter Topology IsManifold MeasureTheory
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelWeakTower
open PhysicalModelTowerFacts PhysicalModelAnnealedRecord PhysicalModelUniformBounds
open KellerLiverani1999

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

section Statement
variable (m₀ m₁ m₂ : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε)) (G : ℝ≥0 → Z → Ω)
  (R ρ₀ ρ₁ weak₀ weak₁ : ℝ)

theorem pairStatement_of_words_scale (hnormH : ∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖)
    (hnorm₀ : ∀ c, ‖m₀.qW c‖ = ‖m₂.qa c‖) (hnorm₁ : ∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖)
    (compactH : IsCompactOperator m₀.inclusionH) (compactW₀ : IsCompactOperator m₀.inclusionW)
    (compactW₁ : IsCompactOperator m₁.inclusionW)
    (hreg₀₁ : m₀.regularCore = m₁.regularCore) (hview₀₁ : m₀.view = m₁.view)
    (hmaps₀₁ : m₀.maps = m₁.maps) (hweight₀₁ : m₀.weight = m₁.weight)
    (hreg₀₂ : m₀.regularCore = m₂.regularCore) (hview₀₂ : m₀.view = m₂.view)
    (hmaps₀₂ : m₀.maps = m₂.maps) (hweight₀₂ : m₀.weight = m₂.weight)
    (hreg₁₂ : m₁.regularCore = m₂.regularCore) (hview₁₂ : m₁.view = m₂.view)
    (hmaps₁₂ : m₁.maps = m₂.maps) (hweight₁₂ : m₁.weight = m₂.weight)
    {L₀ L₁ L₂ : ℝ} (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (bound₀ : PhysicalModelAnalytic.AnalyticBound m₀ L₀)
    (bound₁ : PhysicalModelAnalytic.AnalyticBound m₁ L₁)
    (bound₂ : PhysicalModelAnalytic.AnalyticBound m₂ L₂)
    (src₀ : PhysicalManifoldNoiseSources.Data m₀) (src₁ : PhysicalManifoldNoiseSources.Data m₁)
    (src₂ : PhysicalManifoldNoiseSources.Data m₂)
    (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (contG : ∀ ε, Continuous (G ε))
    (closeG : Tendsto (fun p : ℝ≥0 × Z => G p.1 p.2) ((𝓝 0) ×ˢ ⊤) (𝓝 a₀))
    (η : ℝ≥0) (positiveη : 0 < η) (N : ℕ) (positiveN : 0 < N) (ρ B X : ℝ)
    (positiveρ : 0 < ρ) (nonnegativeB : 0 ≤ B) (Ctrl : ℝ≥0 → Type*)
    (letterF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → Ctrl ε → Ω)
    (resc : ∀ ε : ℝ≥0, 0 < ε → Z → Ctrl ε) (zeroC : Ctrl η)
    (hG : ∀ ε hp hl z, G ε z = letterF ε hp hl (resc ε hp z))
    (hG0' : ∀ z, G 0 z = letterF η positiveη le_rfl zeroC)
    (words₀ : ∀ ε hp hl (control : Fin N → Ctrl ε),
      WordBound m₀ (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B)
    (words₁ : ∀ ε hp hl (control : Fin N → Ctrl ε),
      WordBound m₁ (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B)
    (scale : ℝ) (scaleOne : 1 ≤ scale) (ρscale : ρ < scale) :
    PairStatement m₀ m₁ m₂ law hprob G scale ρ ρ (max L₂ (max ρ X) + 1)
      (max L₂ (max ρ X) + 1) := by
  have rates := pair_rates ρ L₂ X
  have compat₀ := PhysicalModelAnalytic.intertwining m₀ m₂ hreg₀₂ hview₀₂ hmaps₀₂ hweight₀₂
    (towerInclusion m₀ m₂ hnorm₀) (towerInclusion_core m₀ m₂ hnorm₀) bound₀ bound₂
  have compat₁ := PhysicalModelAnalytic.intertwining m₁ m₂ hreg₁₂ hview₁₂ hmaps₁₂ hweight₁₂
    (towerInclusion m₁ m₂ hnorm₁) (towerInclusion_core m₁ m₂ hnorm₁) bound₁ bound₂
  have core₀ := PhysicalModelAnalytic.core_continuous m₀ bound₀ src₀
  have core₁ := PhysicalModelAnalytic.core_continuous m₁ bound₁ src₁
  have core₂ := PhysicalModelAnalytic.core_continuous m₂ bound₂ src₂
  have record₀ := rateRecord_of_words m₀ m₂ law hprob (towerInclusion m₀ m₂ hnorm₀)
    (towerInclusion_compact m₀ m₂ hnorm₀ compactW₀) compat₀ L₀ L₂ hL₀ hL₂
    (PhysicalModelAnalytic.generatorBound m₀ bound₀ hL₀)
    (PhysicalModelAnalytic.generatorBound m₂ bound₂ hL₂) G a₀ G0 contG closeG core₀ core₂ η
    positiveη N positiveN ρ B _ _ positiveρ nonnegativeB rates.1 rates.2.1 scaleOne
    ρscale (towerInclusion_norm m₀ m₂ hnorm₀) Ctrl letterF resc zeroC hG hG0' words₀
  have record₁ := rateRecord_of_words m₁ m₂ law hprob (towerInclusion m₁ m₂ hnorm₁)
    (towerInclusion_compact m₁ m₂ hnorm₁ compactW₁) compat₁ L₁ L₂ hL₁ hL₂
    (PhysicalModelAnalytic.generatorBound m₁ bound₁ hL₁)
    (PhysicalModelAnalytic.generatorBound m₂ bound₂ hL₂) G a₀ G0 contG closeG core₁ core₂ η
    positiveη N positiveN ρ B _ _ positiveρ nonnegativeB rates.1 rates.2.1 scaleOne
    ρscale (towerInclusion_norm m₁ m₂ hnorm₁) Ctrl letterF resc zeroC hG hG0' words₁
  exact pairStatement_of m₀ m₁ m₂ law hprob G _ _ _ _ _ hnormH hnorm₀ hnorm₁ compactH compactW₁
    hreg₀₁ hview₀₁ hmaps₀₁ hweight₀₁ bound₀ bound₁ record₀ record₁

end Statement

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
