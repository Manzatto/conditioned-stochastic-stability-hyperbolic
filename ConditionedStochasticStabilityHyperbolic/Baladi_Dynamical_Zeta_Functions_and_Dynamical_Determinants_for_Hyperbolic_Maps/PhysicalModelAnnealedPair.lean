module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTowerFacts
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedRecord
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedQuantitativeAnnealedPair
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedCompatibility
meta import Lean.LibrarySuggestions.Basic

/-! Three physical models `m₀, m₁, m₂` (strong, middle, weak stage) sharing the
ordinary data, with the intermediate norms of `m₀` and the weak norms of `m₀`
and `m₁` equal to the strong norms of `m₁` resp. `m₂`, give the analytic pair
consumed by local stochastic stability, from the two carrier records with the
same law, letters and scale. The strong record is read along `j ∘ i`, which is
the weak tower inclusion of `m₀` by the core identities. The records also
retain their principal and weak rates. -/
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelAnnealedPair"

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

/-- Generator compatibility from pointwise intertwining of their identified forms. -/
theorem compat_of_eq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (i : X →L[ℂ] Y) {A A' : X →L[ℂ] X}
    {B B' : Y →L[ℂ] Y} (hA : A = A') (hB : B = B') (h : ∀ x, i (A' x) = B' (i x)) :
    i.comp A = B.comp i := by
  subst hA
  subst hB
  ext x
  exact h x

section Rates
variable (m n : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε))
  (j : m.StrongSpace →L[ℂ] n.StrongSpace)

/-- A carrier record which also records its principal and weak rates. -/
def RateRecord (G : ℝ≥0 → Z → Ω) (scale ρ weakRate : ℝ) : Prop :=
  IsCompactOperator j ∧ ∃ r : ActualAnnealedInputs law hprob j scale,
    (∀ ε z, r.generator ε z = m.generator (G ε z)) ∧ r.principal = ρ ∧ r.weakRate = weakRate

theorem rateRecord_of_words (compact : IsCompactOperator j)
    (compat : ∀ a x, j (m.generator a x) = n.generator a (j x))
    (Lm Ln : ℝ) (hLm : 0 ≤ Lm) (hLn : 0 ≤ Ln)
    (boundM : GeneratorBound m Lm) (boundN : GeneratorBound n Ln)
    (G : ℝ≥0 → Z → Ω) (a₀ : Ω) (G0 : ∀ z, G 0 z = a₀) (contG : ∀ ε, Continuous (G ε))
    (closeG : Tendsto (fun p : ℝ≥0 × Z => G p.1 p.2) ((𝓝 0) ×ˢ ⊤) (𝓝 a₀))
    (coreM : ∀ c, Continuous (fun a => m.generator a (coreLift m.qa c)))
    (coreN : ∀ c, Continuous (fun a => n.generator a (coreLift n.qa c)))
    (η : ℝ≥0) (positiveη : 0 < η) (N : ℕ) (positiveN : 0 < N) (ρ B weakRate scale : ℝ)
    (positiveρ : 0 < ρ) (nonnegativeB : 0 ≤ B) (ρweak : ρ < weakRate) (weakLn : Ln ≤ weakRate)
    (scaleOne : 1 ≤ scale) (ρscale : ρ < scale)
    (hj : ∀ x, ‖j x‖ = ‖m.inclusionW x‖) (Ctrl : ℝ≥0 → Type*)
    (letterF : ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → Ctrl ε → Ω)
    (resc : ∀ ε : ℝ≥0, 0 < ε → Z → Ctrl ε) (zeroC : Ctrl η)
    (hG : ∀ ε hp hl z, G ε z = letterF ε hp hl (resc ε hp z))
    (hG0' : ∀ z, G 0 z = letterF η positiveη le_rfl zeroC)
    (words : ∀ ε hp hl (control : Fin N → Ctrl ε),
      WordBound m (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B) :
    RateRecord m n law hprob j G scale ρ weakRate :=
  ⟨compact, record m n law hprob j compact compat Lm Ln hLm hLn boundM boundN G a₀ G0 contG closeG
    coreM coreN η positiveη N positiveN ρ B weakRate scale positiveρ nonnegativeB ρweak weakLn
    scaleOne ρscale (PhysicalModelLetterBlocks.block_of_words m j hj Ctrl η positiveη letterF resc
      zeroC G hG hG0' N ρ B words), fun _ _ => rfl, rfl, rfl⟩

/-- Records transport along an equality of inclusions (at the level of propositions). -/
theorem rateRecord_congr {j' : m.StrongSpace →L[ℂ] n.StrongSpace} (h : j = j')
    {G : ℝ≥0 → Z → Ω} {scale ρ weakRate : ℝ} (r : RateRecord m n law hprob j G scale ρ weakRate) :
    RateRecord m n law hprob j' G scale ρ weakRate :=
  h ▸ r

end Rates

section Pair

variable (m₀ m₁ m₂ : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (hnormH : ∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖) (hnorm₀ : ∀ c, ‖m₀.qW c‖ = ‖m₂.qa c‖)
  (hnorm₁ : ∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖)

/-- The tower factorization `j ∘ i = k`. -/
theorem factor : (towerInclusion m₁ m₂ hnorm₁).comp (towerInclusionH m₀ m₁ hnormH) =
    towerInclusion m₀ m₂ hnorm₀ :=
  eq_of_core m₀ m₂ _ _ (fun c => (congrArg (towerInclusion m₁ m₂ hnorm₁)
    (towerInclusionH_core m₀ m₁ hnormH c)).trans (towerInclusion_core m₁ m₂ hnorm₁ c))
    (towerInclusion_core m₀ m₂ hnorm₀)

variable [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε)) (G : ℝ≥0 → Z → Ω)
  (R ρ₀ ρ₁ weak₀ weak₁ : ℝ)

set_option maxHeartbeats 1600000 in
/-- The analytic pair of the three-stage tower, with its rates. -/
def pair (compactH : IsCompactOperator m₀.inclusionH) (compactW : IsCompactOperator m₁.inclusionW)
    (hreg : m₀.regularCore = m₁.regularCore) (hview : m₀.view = m₁.view)
    (hmaps : m₀.maps = m₁.maps) (hweight : m₀.weight = m₁.weight)
    {L₀ L₁ : ℝ} (bound₀ : PhysicalModelAnalytic.AnalyticBound m₀ L₀)
    (bound₁ : PhysicalModelAnalytic.AnalyticBound m₁ L₁)
    (record₀ : RateRecord m₀ m₂ law hprob (towerInclusion m₀ m₂ hnorm₀) G R ρ₀ weak₀)
    (record₁ : RateRecord m₁ m₂ law hprob (towerInclusion m₁ m₂ hnorm₁) G R ρ₁ weak₁) :
    ProducedAnnealedPair.QuantitativeData (towerInclusionH m₀ m₁ hnormH)
      (towerInclusion m₁ m₂ hnorm₁) law hprob (fun ε z => m₀.generator (G ε z))
      (fun ε z => m₁.generator (G ε z)) R ρ₀ ρ₁ weak₀ weak₁ :=
  have record₀' : RateRecord m₀ m₂ law hprob
      ((towerInclusion m₁ m₂ hnorm₁).comp (towerInclusionH m₀ m₁ hnormH)) G R ρ₀ weak₀ :=
    rateRecord_congr m₀ m₂ law hprob _ (factor m₀ m₁ m₂ hnormH hnorm₀ hnorm₁).symm record₀
  { pair :=
    { compactS := towerInclusionH_compact m₀ m₁ hnormH compactH
      injectiveS := towerInclusionH_injective m₀ m₁ hnormH
      denseS := towerInclusionH_denseRange m₀ m₁ hnormH
      compactH := towerInclusion_compact m₁ m₂ hnorm₁ compactW
      injectiveH := towerInclusion_injective m₁ m₂ hnorm₁
      strong := record₀'.2.choose
      intermediate := record₁.2.choose
      strong_generator := record₀'.2.choose_spec.1
      intermediate_generator := record₁.2.choose_spec.1
      compatible := fun ε => record₀'.2.choose.operator_compatibility_of_generators
        record₁.2.choose _ ε fun z =>
          compat_of_eq _ (record₀'.2.choose_spec.1 ε z) (record₁.2.choose_spec.1 ε z)
            (PhysicalModelAnalytic.intertwining m₀ m₁ hreg hview hmaps hweight _
              (towerInclusionH_core m₀ m₁ hnormH) bound₀ bound₁ (G ε z)) }
    principalS_eq := record₀'.2.choose_spec.2.1
    principalH_eq := record₁.2.choose_spec.2.1
    weakRateS_eq := record₀'.2.choose_spec.2.2
    weakRateH_eq := record₁.2.choose_spec.2.2 }

end Pair

section Statement
variable (m₀ m₁ m₂ : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  [MetricSpace Ω] {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
  [OpensMeasurableSpace Z] [SecondCountableTopology Z]
  (law : ℝ≥0 → Measure Z) (hprob : ∀ ε, IsProbabilityMeasure (law ε)) (G : ℝ≥0 → Z → Ω)
  (R ρ₀ ρ₁ weak₀ weak₁ : ℝ)

/-- The three-stage tower carries the analytic pair of its two strong stages. -/
def PairStatement : Prop :=
  ∃ hnormH : (∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖), ∃ hnorm₁ : (∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖),
    Nonempty (ProducedAnnealedPair.QuantitativeData (towerInclusionH m₀ m₁ hnormH)
      (towerInclusion m₁ m₂ hnorm₁) law hprob (fun ε z => m₀.generator (G ε z))
      (fun ε z => m₁.generator (G ε z)) R ρ₀ ρ₁ weak₀ weak₁)

theorem pairStatement_of (hnormH : ∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖)
    (hnorm₀ : ∀ c, ‖m₀.qW c‖ = ‖m₂.qa c‖) (hnorm₁ : ∀ c, ‖m₁.qW c‖ = ‖m₂.qa c‖)
    (compactH : IsCompactOperator m₀.inclusionH) (compactW : IsCompactOperator m₁.inclusionW)
    (hreg : m₀.regularCore = m₁.regularCore) (hview : m₀.view = m₁.view)
    (hmaps : m₀.maps = m₁.maps) (hweight : m₀.weight = m₁.weight)
    {L₀ L₁ : ℝ} (bound₀ : PhysicalModelAnalytic.AnalyticBound m₀ L₀)
    (bound₁ : PhysicalModelAnalytic.AnalyticBound m₁ L₁)
    (record₀ : RateRecord m₀ m₂ law hprob (towerInclusion m₀ m₂ hnorm₀) G R ρ₀ weak₀)
    (record₁ : RateRecord m₁ m₂ law hprob (towerInclusion m₁ m₂ hnorm₁) G R ρ₁ weak₁) :
    PairStatement m₀ m₁ m₂ law hprob G R ρ₀ ρ₁ weak₀ weak₁ :=
  ⟨hnormH, hnorm₁, ⟨pair m₀ m₁ m₂ hnormH hnorm₀ hnorm₁ law hprob G R ρ₀ ρ₁ weak₀ weak₁ compactH
    compactW hreg hview hmaps hweight bound₀ bound₁ record₀ record₁⟩⟩

theorem pair_rates (ρ L X : ℝ) :
    ρ < max L (max ρ X) + 1 ∧ L ≤ max L (max ρ X) + 1 ∧ 1 ≤ max 1 (ρ + 1) ∧ ρ < max 1 (ρ + 1) := by
  refine ⟨?_, ?_, le_max_left _ _, lt_of_lt_of_le (lt_add_one ρ) (le_max_right _ _)⟩
  · linarith [le_max_left ρ X, le_max_right L (max ρ X)]
  · linarith [le_max_left L (max ρ X)]

/-- The pair statement from the one-step bounds, noise sources and block words of the three
stages, all at once (so that a concrete carrier needs a single application). -/
theorem pairStatement_of_words (hnormH : ∀ c, ‖m₀.qH c‖ = ‖m₁.qa c‖)
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
      WordBound m₁ (List.ofFn fun k => letterF ε hp hl (control k)) (ρ ^ N) B) :
    PairStatement m₀ m₁ m₂ law hprob G (max 1 (ρ + 1)) ρ ρ (max L₂ (max ρ X) + 1)
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
    positiveη N positiveN ρ B _ _ positiveρ nonnegativeB rates.1 rates.2.1 rates.2.2.1
    rates.2.2.2 (towerInclusion_norm m₀ m₂ hnorm₀) Ctrl letterF resc zeroC hG hG0' words₀
  have record₁ := rateRecord_of_words m₁ m₂ law hprob (towerInclusion m₁ m₂ hnorm₁)
    (towerInclusion_compact m₁ m₂ hnorm₁ compactW₁) compat₁ L₁ L₂ hL₁ hL₂
    (PhysicalModelAnalytic.generatorBound m₁ bound₁ hL₁)
    (PhysicalModelAnalytic.generatorBound m₂ bound₂ hL₂) G a₀ G0 contG closeG core₁ core₂ η
    positiveη N positiveN ρ B _ _ positiveρ nonnegativeB rates.1 rates.2.1 rates.2.2.1
    rates.2.2.2 (towerInclusion_norm m₁ m₂ hnorm₁) Ctrl letterF resc zeroC hG hG0' words₁
  exact pairStatement_of m₀ m₁ m₂ law hprob G _ _ _ _ _ hnormH hnorm₀ hnorm₁ compactH compactW₁
    hreg₀₁ hview₀₁ hmaps₀₁ hweight₀₁ bound₀ bound₁ record₀ record₁

end Statement

end ConditionedStochasticStabilityHyperbolic.PhysicalModelAnnealedPair
