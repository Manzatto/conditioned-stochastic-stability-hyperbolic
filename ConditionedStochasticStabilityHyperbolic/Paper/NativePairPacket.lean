module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePairLocalStability
public import ConditionedStochasticStabilityHyperbolic.Paper.NativePacketOfPair
public import ConditionedStochasticStabilityHyperbolic.Global.ScaleSourcesCongr
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusFrom
meta import Lean.LibrarySuggestions.Basic

/-! The native packet and selection of an identified pair of abstract physical models. The raw
radius bound, the contour of the leading record and the transported physical sources are
assembled while the models stay abstract; a concrete carrier supplies its radius bound, spectrum
comparison and sources. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativePairPacket"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter MeasureTheory Bundle IsManifold
open scoped Topology NNReal BoundedContinuousFunction Manifold ContDiff ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativePairPacket
open LeanShared LeanShared.TwoNormNormalization
open KellerLiverani1999 PhysicalManifoldModel PhysicalModelHorizonIdentities PhysicalModelAnnealedPair
open NativePairLocalStability

variable {E U X AtlasIndex Reg A Ω Parameters ι Z Zret Core : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {VD SD : Set X} {μ : Measure U} [μ.IsAddHaarMeasure]
  [MetricSpace Ω] [MetricSpace Parameters] [Fintype ι]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  {evaluate : Parameters → X → X} {g : X → ℝ} {Λ : Set X}

set_option maxHeartbeats 1000000 in
/-- The native packet of an identified pair. -/
def pairPacket
    (K : Set X) [CompactSpace K] (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    (L : RegularNoise.Laws (ι := ι)) (R : ℝ)
    (m₀ m₁ m₂ : Data (E := E) (U := U) (M := X) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) VD SD μ)
    (Gp : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → Ω) {ρ weakRate : ℝ}
    (hnormH : NormIdH m₀ m₁) (hnorm₁ : NormIdW m₁ m₂)
    (q : PairData m₀ m₁ m₂ L.fixedLaw (fun _ => inferInstance) Gp R ρ ρ weakRate weakRate
      hnormH hnorm₁)
    [Nontrivial m₁.StrongSpace] (a₀ : Ω) (hG0 : ∀ z, Gp 0 z = a₀) (P0 : ℝ)
    (principal : ρ ≤ Real.exp P0)
    (upper : PhysicalModelNativeRadiusUpper.RadiusFrom m₁ a₀ P0 m₂.StrongSpace)
    (comparison : NativeLayerComparison.SpectrumComparison C R q.pair.intermediate.principal
      q.pair.intermediate.operator) :
    NativeNullPrefixSources.NativePacket K C L.fixedLaw (fun _ => inferInstance) R P0 :=
  NativeNullPrefixSources.packetOfPair K C q
    (PhysicalModelTowerFacts.towerInclusion_denseRange _ _ hnorm₁) P0 (m₁.generator a₀)
    (fun z => congrArg m₁.generator (hG0 z))
    (NativeNullPrefixSources.radius_of_raw q _ (fun z => congrArg m₁.generator (hG0 z)) P0
      (fun k hk α R' C D hα hR' hC hD two rate => upper k hk α R' C D hα hR' hC hD two rate)
      principal)
    principal comparison

set_option maxHeartbeats 1000000 in
/-- The selection of the native packet of an identified pair, with the transported sources. -/
def pairSelection
    (K : Set X) [CompactSpace K] (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    (L : RegularNoise.Laws (ι := ι)) (R : ℝ)
    (m₀ m₁ m₂ : Data (E := E) (U := U) (M := X) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) VD SD μ)
    (Gp : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → Ω) {ρ weakRate : ℝ}
    (hnormH : NormIdH m₀ m₁) (hnorm₁ : NormIdW m₁ m₂)
    (q : PairData m₀ m₁ m₂ L.fixedLaw (fun _ => inferInstance) Gp R ρ ρ weakRate weakRate
      hnormH hnorm₁)
    [Nontrivial m₁.StrongSpace] (a₀ : Ω) (hG0 : ∀ z, Gp 0 z = a₀) (P0 : ℝ)
    (principal : ρ ≤ Real.exp P0)
    (upper : PhysicalModelNativeRadiusUpper.RadiusFrom m₁ a₀ P0 m₂.StrongSpace)
    (comparison : NativeLayerComparison.SpectrumComparison C R q.pair.intermediate.principal
      q.pair.intermediate.operator)
    (T : X ≃ₜ X) (V G : Set X) (hK : IsCompact K)
    (F F' : ℝ≥0 → X × RegularNoise.FixedControl (ι := ι) → X)
    (hF : ∀ ε, Measurable (F ε)) (hF' : ∀ ε, Measurable (F' ε))
    (heq : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, F ε = F' ε)
    (w wc : K → ℝ) (hw : Continuous w) (hwc : Measurable wc) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (dm : DeterministicLeading (q.pair.intermediate.operator 0))
    (rateH : dm.rate = R⁻¹ * Real.exp P0) (below : ρ < Real.exp P0)
    (weak : Real.exp P0 ≤ weakRate)
    (Mt : SmoothPhysicalTests.tests (E := E) K → m₁.StrongSpace →L[ℂ] m₁.StrongSpace)
    (hcutoff₁ : ∀ i x, conj (m₁.localization.cutoff i x) = m₁.localization.cutoff i x)
    (hangle₁ : ∀ i ξ, (m₁.angle i).toFun (-ξ) = (m₁.angle i).toFun ξ)
    (Jreg₁ : Reg →L[ℝ] Reg) (hJreg₁ : ∀ v x, m₁.view (Jreg₁ v) x = star (m₁.view v x))
    {L₁ : ℝ} (bound₁ : PhysicalModelAnalytic.AnalyticBound m₁ L₁)
    (sources :
      letI : NormedAddCommGroup m₁.StrongSpace := m₁.strongNormedParent
      letI : SeminormedAddCommGroup m₁.StrongSpace := m₁.strongSeminormedParent
      letI : NormedSpace ℂ m₁.StrongSpace := m₁.strongScalarParent
      letI : UniformSpace m₁.StrongSpace := m₁.strongCarrierUniform
      letI : CompleteSpace m₁.StrongSpace := m₁.strongCarrierComplete
      letI : NormedAddCommGroup m₂.StrongSpace := m₂.strongNormedParent
      letI : SeminormedAddCommGroup m₂.StrongSpace := m₂.strongSeminormedParent
      letI : NormedSpace ℂ m₂.StrongSpace := m₂.strongScalarParent
      letI : UniformSpace m₂.StrongSpace := m₂.strongCarrierUniform
      letI : CompleteSpace m₂.StrongSpace := m₂.strongCarrierComplete
      ∀ (j : m₁.StrongSpace →L[ℂ] m₂.StrongSpace)
        (inputs : ActualAnnealedInputs L.fixedLaw (fun _ => inferInstance) j R),
        (∀ ε z, inputs.generator ε z = m₁.generator (Gp ε z)) →
        Function.Injective j → IsCompactOperator j →
        ∀ {det : DeterministicLeading (inputs.operator 0)} {q' δ : ℝ}
          (o : ProjectorOutputs inputs.operator (weakEmbedding j) det q' δ),
          δ < q' - det.subordinate → δ < det.rate - q' → 0 < q' →
          inputs.principal / R < q' →
          (∀ ε, RealOperatorConjugation (inputs.operator ε)) →
          ∀ ζ : ℝ, 0 < ζ → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
            Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret)
              (Core := Core) T V K G hK (L.fixedLaw ε) (F ε) (hF ε)
              w hw wc hwc R hR hwR hwcR o ε ζ (SmoothPhysicalTests.tests (E := E) K) Mt)) :
    NativeNullPrefixSources.NativeSelection
      (pairPacket K C L R m₀ m₁ m₂ Gp hnormH hnorm₁ q a₀ hG0 P0 principal upper comparison)
      T V G hK L.fixedLaw F' hF' w wc hw hwc hR hwR hwcR :=
  have rates := NativeNullPrefixSources.selected_rates q dm P0 rateH below weak
  NativeNullPrefixSources.selectionOfPair (Z := Z) (Zret := Zret) (Core := Core) K C q
    (PhysicalModelTowerFacts.towerInclusion_denseRange _ _ hnorm₁) P0 (m₁.generator a₀)
    (fun z => congrArg m₁.generator (hG0 z))
    (NativeNullPrefixSources.radius_of_raw q _ (fun z => congrArg m₁.generator (hG0 z)) P0
      (fun k hk α R' C D hα hR' hC hD two rate => upper k hk α R' C D hα hR' hC hD two rate)
      principal)
    principal comparison T V G hK L.fixedLaw F' hF' w wc hw hwc hR hwR hwcR dm rates.1 rates.2.1
    rates.2.2 (SmoothPhysicalTests.tests (E := E) K) Mt
    (fun outputs ζ hζ => by
      let cm := contourParameters dm _ _ rates.1 rates.2.1
      have src := pair_sources_of_cached T V K G hK L F hF w hw wc hwc R hR hwR hwcR m₀ m₁ m₂ Gp
        hnormH hnorm₁ q Mt sources outputs cm.radius_subordinate cm.radius_leading cm.cutoff_pos
        cm.principal_lt
        (fun ε => PhysicalModelRealStructure.actualConjugation m₁ hcutoff₁ hangle₁ Jreg₁ hJreg₁
          bound₁ q.pair.intermediate Gp q.pair.intermediate_generator ε) ζ hζ
      filter_upwards [src, heq] with ε hs hg
      exact Global.NoFullSupportKLFamily.ScaleSources.congr T V K G hK (hF ε) (hF' ε) _ _ _ _
        R hR _ _ outputs ε ζ _ _ rfl hg hs)

end ConditionedStochasticStabilityHyperbolic.Paper.NativePairPacket
