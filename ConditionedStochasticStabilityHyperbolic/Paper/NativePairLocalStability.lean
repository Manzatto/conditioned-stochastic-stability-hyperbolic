module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportLocalRetention
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalEquilibriumIdentification
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelPairNativeIdentification
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelRealStructure
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerComparison
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
meta import Lean.LibrarySuggestions.Basic

/-! Literal local stability and gap retention from an identified native pair of abstract physical
models (thm:local and thm:qem-local, consumer form). The leading records, their rates, the real
structures of the averaged operators and the equilibrium identification on the collar are all
produced here while the three models stay abstract; a concrete carrier supplies its identified pair,
its realness data and its eventual physical scale sources. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativePairLocalStability"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter MeasureTheory Bundle IsManifold
open scoped Topology NNReal BoundedContinuousFunction Manifold ContDiff ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativePairLocalStability
open LeanShared LeanShared.ControlledPlaqueClosure LeanShared.TwoNormNormalization
open KellerLiverani1999 PhysicalManifoldModel PhysicalModelHorizonIdentities PhysicalModelAnnealedPair

/-- A principal bound below a normalized leading rate. -/
theorem rate_lt {a b c d R : ℝ} (h1 : a = b) (h2 : d = R⁻¹ * c) (hbc : b < c) (hR : 0 < R) :
    a / R < d := by
  rw [h1, h2, div_eq_inv_mul]
  exact mul_lt_mul_of_pos_left hbc (inv_pos.mpr hR)

/-- A normalized leading rate below a weak rate. -/
theorem rate_le {a b c d R : ℝ} (h1 : a = b) (h2 : d = R⁻¹ * c) (hcb : c ≤ b) (hR : 0 < R) :
    d ≤ a / R := by
  rw [h1, h2, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hcb (inv_nonneg.mpr hR.le)

section Accessors
variable {S H W Z : Type*} {iS : NormedAddCommGroup S} {sS : NormedSpace ℂ S}
  {iH : NormedAddCommGroup H} {sH : NormedSpace ℂ H} {iW : NormedAddCommGroup W}
  {sW : NormedSpace ℂ W} {mZ : MeasurableSpace Z} {i : S →L[ℂ] H} {j : H →L[ℂ] W}
  {law : ℝ≥0 → Measure Z} {prob : ∀ ε, IsProbabilityMeasure (law ε)}
  {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H} {R pS pH wS wH : ℝ}

/-- The instances recorded in the type of quantitative pair data. -/
@[reducible] def normedH (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedAddCommGroup H := iH

@[reducible, inherit_doc normedH] def scalarH
    (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedSpace ℂ H := sH

@[reducible, inherit_doc normedH] def normedS
    (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedAddCommGroup S := iS

@[reducible, inherit_doc normedH] def scalarS
    (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedSpace ℂ S := sS

@[reducible, inherit_doc normedH] def normedW
    (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedAddCommGroup W := iW

@[reducible, inherit_doc normedH] def scalarW
    (_q : ProducedAnnealedPair.QuantitativeData i j law prob genS genH R pS pH wS wH) :
    NormedSpace ℂ W := sW

end Accessors

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
/-- The spectrum comparison of a carrier gives the comparison for the intermediate inputs of the
identified pair data. -/
theorem pair_comparison_of_cached {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (L : RegularNoise.Laws (ι := ι)) (R : ℝ)
    (m₀ m₁ m₂ : Data (E := E) (U := U) (M := X) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) VD SD μ)
    (Gp : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → Ω) {ρ₀ ρ₁ weak₀ weak₁ : ℝ}
    (hnormH : NormIdH m₀ m₁) (hnorm₁ : NormIdW m₁ m₂)
    (q : PairData m₀ m₁ m₂ L.fixedLaw (fun _ => inferInstance) Gp R ρ₀ ρ₁ weak₀ weak₁
      hnormH hnorm₁)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain Y)
    (comparison :
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
        Nontrivial m₁.StrongSpace ∧
          NativeLayerComparison.SpectrumComparison C R inputs.principal inputs.operator) :
    Nontrivial m₁.StrongSpace ∧
      NativeLayerComparison.SpectrumComparison C R q.pair.intermediate.principal
        q.pair.intermediate.operator := by
  have step := comparison _ q.pair.intermediate q.pair.intermediate_generator q.pair.injectiveH
    q.pair.compactH
  exact step

set_option maxHeartbeats 1000000 in
/-- The eventual physical sources of a carrier give the sources for the intermediate inputs of the
identified pair data. -/
theorem pair_sources_of_cached
    (T : X ≃ₜ X) (V K G : Set X) [CompactSpace K] (hK : IsCompact K)
    (L : RegularNoise.Laws (ι := ι))
    (F : ℝ≥0 → X × RegularNoise.FixedControl (ι := ι) → X) (hF : ∀ ε, Measurable (F ε))
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (m₀ m₁ m₂ : Data (E := E) (U := U) (M := X) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) VD SD μ)
    (Gp : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → Ω) {ρ weakRate : ℝ}
    (hnormH : NormIdH m₀ m₁) (hnorm₁ : NormIdW m₁ m₂)
    (q : PairData m₀ m₁ m₂ L.fixedLaw (fun _ => inferInstance) Gp R ρ ρ weakRate weakRate
      hnormH hnorm₁)
    (Mt : SmoothPhysicalTests.tests (E := E) K → m₁.StrongSpace →L[ℂ] m₁.StrongSpace)
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
    ∀ {det : DeterministicLeading (q.pair.intermediate.operator 0)} {q' δ : ℝ}
      (o : ProjectorOutputs q.pair.intermediate.operator
        (weakEmbedding (PhysicalModelWeakTower.towerInclusion m₁ m₂ hnorm₁)) det q' δ),
      δ < q' - det.subordinate → δ < det.rate - q' → 0 < q' →
      q.pair.intermediate.principal / R < q' →
      (∀ ε, RealOperatorConjugation (q.pair.intermediate.operator ε)) →
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
        Nonempty (Global.NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret)
          (Core := Core) T V K G hK (L.fixedLaw ε) (F ε) (hF ε)
          w hw wc hwc R hR hwR hwcR o ε ζ (SmoothPhysicalTests.tests (E := E) K) Mt) := by
  intro det q' δ o h1 h2 h3 h4 hconj
  have step := sources _ q.pair.intermediate q.pair.intermediate_generator q.pair.injectiveH
    q.pair.compactH o h1 h2 h3 h4 hconj
  exact step

set_option maxHeartbeats 1000000 in
/-- Local stability and gap retention from an identified native pair. -/
theorem native_pair_stability
    (T : X ≃ₜ X) (V K G B : Set X) [CompactSpace K]
    (hHL : HL (E := E) T g Λ V) (hΛ : isolatedCore T K = Λ)
    (e : HyperbolicBasicSet.EquilibriumPackage hHL.basic.hyperbolic g)
    (φ : X → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hB : IsOpen B)
    (hcoreB : isolatedCore T K ⊆ B) (hBV : closure B ⊆ V) (hBG : closure B ⊆ G)
    (hsep : (T '' closure B) ∩ forwardTrapped T K ⊆ B)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (hcore : (isolatedCore T K).Nonempty)
    (N : RegularNoise.Maps (E := E) (ι := ι) T hHL.r) (L : RegularNoise.Laws (ι := ι))
    (representation : RegularNoise.Representation N Parameters evaluate)
    (hF : ∀ ε : ℝ≥0, Measurable (fun z : X × RegularNoise.FixedControl (ι := ι) =>
      evaluate (representation.fixedParameters ε z.2) z.1))
    (w : K → ℝ) (hw : Continuous w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    (m₀ m₁ m₂ : Data (E := E) (U := U) (M := X) (AtlasIndex := AtlasIndex) (Reg := Reg)
      (LocalReg := LocalReg) (A := A) (Ω := Ω) VD SD μ)
    (Gp : ℝ≥0 → RegularNoise.FixedControl (ι := ι) → Ω) {ρ weakRate lam : ℝ}
    (state : ProbabilityMeasure X)
    (pair : NativePairIdentified m₀ m₁ m₂ L.fixedLaw (fun _ => inferInstance) Gp R ρ ρ weakRate
      weakRate lam (fun ψ => ∫ x, ψ.1 x ∂(state : Measure X)))
    (belowP : ρ < lam) (hweak : lam ≤ weakRate) (stateEq : e.state = state)
    (hcutoff₀ : ∀ i x, conj (m₀.localization.cutoff i x) = m₀.localization.cutoff i x)
    (hangle₀ : ∀ i ξ, (m₀.angle i).toFun (-ξ) = (m₀.angle i).toFun ξ)
    (Jreg₀ : Reg →L[ℝ] Reg) (hJreg₀ : ∀ v x, m₀.view (Jreg₀ v) x = star (m₀.view v x))
    {L₀ : ℝ} (bound₀ : PhysicalModelAnalytic.AnalyticBound m₀ L₀)
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
              (Core := Core) T V K G hK (L.fixedLaw ε)
              (fun z : X × RegularNoise.FixedControl (ι := ι) =>
                evaluate (representation.fixedParameters ε z.2) z.1) (hF ε)
              w hw wc hwc R hR hwR hwcR o ε ζ (SmoothPhysicalTests.tests (E := E) K)
              (fun t => strongMultiplier m₁ (SmoothPhysicalTests.extension K t)
                (SmoothPhysicalTests.extension_smooth K t)))) :
    LocalConclusions.Stability N L K Λ hK.measurableSet w hw.measurable R hR hwR
      (fun x => φ x - Real.log (hHL.basic.hyperbolic.unstableJacobian x)) ∧
    LocalConclusions.GapRetention N L K Λ hK.measurableSet w hw.measurable R hR hwR := by
  obtain ⟨hnormH, hnorm₁, q, ds, dm, rateS, rateH, ident⟩ := pair
  have hprincipalS := rate_lt q.principalS_eq rateS belowP hR
  have hweakS := rate_le q.weakRateS_eq rateS hweak hR
  have hprincipalH := rate_lt q.principalH_eq rateH belowP hR
  have hweakH := rate_le q.weakRateH_eq rateH hweak hR
  have hΛK : Λ ⊆ K := by
    rw [← hΛ]; exact hcoreB.trans ((subset_closure.trans hBV).trans hVK)
  refine HLNoFullSupportProducedLocalStability.stability_and_gapRetention_from_produced_pair
    (Z := Z) (Zret := Zret) (Core := Core)
    T V K G B hHL hΛ e φ hφ hV hVK hK hB hcoreB hBV hBG hsep hcoreG htrans hcore N L
    representation hF w hw hwG wc hwc R hR hwR hwcR _ _ q.pair
    essentialRadiusContract essentialRadiusContract classicalContract classicalContract
    ds dm hprincipalS hweakS hprincipalH hweakH
    (SmoothPhysicalTests.tests (E := E) K) (SmoothPhysicalTests.dense K hK.isClosed)
    (fun t => strongMultiplier m₁ (SmoothPhysicalTests.extension K t)
      (SmoothPhysicalTests.extension_smooth K t))
    (rateS.trans rateH.symm) ?conjS ?conjH ?srcs ?ident
  case conjS =>
    exact fun ε => ⟨PhysicalModelRealStructure.actualConjugation m₀ hcutoff₀ hangle₀ Jreg₀ hJreg₀
      bound₀ q.pair.strong Gp q.pair.strong_generator ε⟩
  case conjH =>
    exact fun ε => ⟨PhysicalModelRealStructure.actualConjugation m₁ hcutoff₁ hangle₁ Jreg₁ hJreg₁
      bound₁ q.pair.intermediate Gp q.pair.intermediate_generator ε⟩
  case srcs =>
    intro om
    let cm := contourParameters dm _ _ hprincipalH hweakH
    have step := sources _ q.pair.intermediate q.pair.intermediate_generator q.pair.injectiveH
      q.pair.compactH om cm.radius_subordinate cm.radius_leading cm.cutoff_pos cm.principal_lt
      (fun ε => PhysicalModelRealStructure.actualConjugation m₁ hcutoff₁ hangle₁ Jreg₁ hJreg₁
        bound₁ q.pair.intermediate Gp q.pair.intermediate_generator ε)
    exact step
  case ident =>
    intro f
    have collarIntegral := LocalEquilibriumIdentification.integral_on_collar K
      (hHL.stateOnCollar e K hK.measurableSet hΛK) e.state
      (hHL.stateOnCollar_map e K hK.measurableSet hΛK) f.val
      (SmoothPhysicalTests.extension K f)
      (SmoothPhysicalTests.extension_smooth K f).continuous
      (fun x => (SmoothPhysicalTests.extension_live K f x).symm)
    have step1 := ident ⟨SmoothPhysicalTests.extension K f,
      SmoothPhysicalTests.extension_smooth K f⟩
    have step2 := collarIntegral.trans ((congrArg (fun ν : ProbabilityMeasure X =>
      ∫ x, SmoothPhysicalTests.extension K f x ∂(ν : Measure X)) stateEq).trans step1.symm)
    exact step2

end ConditionedStochasticStabilityHyperbolic.Paper.NativePairLocalStability
