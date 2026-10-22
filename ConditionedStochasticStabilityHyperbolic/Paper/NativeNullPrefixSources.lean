module

public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalNullPacketApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerSpectrum
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedGlobalAgreement
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalNoiseDensity
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import ConditionedStochasticStabilityHyperbolic.Global.BoundaryNullDensityReference
public import ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.UltraFellerSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.SquareCompactFredholmSource

/-! Native assembly of the eventual prefix sources (global route, native carriers). Every layer
supplies an analytic packet with only an UPPER bound of the deterministic spectral radius at the
pressure (no mixing, no leading record on subordinate layers); the selected layer supplies the
leading record, the contour data and its physical sources. The global stochastic inputs (strong
Feller germ, shifted-filtration support, target absorption, density, eigencomparison) are derived
from one representation of the actual noise, exactly as in the ordinary-source assembly. -/

public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory ProbabilityTheory IsManifold
open scoped Topology NNReal Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
open LeanShared Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open KellerLiverani1999 ComplexStrongFeller RestrictedLayerChain
open FiltrationPressureConfinement LeanShared.ControlledPlaqueClosure
universe uS uW uZ uZret uCore

/-- An analytic packet of one closed layer with an upper radius bound at the pressure. -/
structure NativePacket {X Ξ : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Ξ] (K : Set X) [CompactSpace K]
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K)
    (law : ℝ≥0 → Measure Ξ) (probability : ∀ ε, IsProbabilityMeasure (law ε))
    (scale pressure : ℝ) where
  Strong : Type uS
  [strongNormed : NormedAddCommGroup Strong]
  [strongScalar : NormedSpace ℂ Strong]
  [strongComplete : CompleteSpace Strong]
  [strongNontrivial : Nontrivial Strong]
  Weak : Type uW
  [weakNormed : NormedAddCommGroup Weak]
  [weakScalar : NormedSpace ℂ Weak]
  [weakComplete : CompleteSpace Weak]
  inclusion : Strong →L[ℂ] Weak
  generator : ℝ≥0 → Ξ → Strong →L[ℂ] Strong
  model : ProducedAnnealedModel.Data inclusion inclusion law probability generator scale
  essential : EssentialRadiusContract (E := Strong) (W := Weak)
  confinement : ClassicalConfinementContract (E := Strong) (W := Weak)
  radius_le : spectralRadius ℂ ((scale : ℂ) • model.inputs.operator 0) ≤
    ENNReal.ofReal (Real.exp pressure)
  principal_le : model.inputs.principal ≤ Real.exp pressure
  spectrumComparison : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
    ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
      (scale • transferOperator (𝕜 := ℂ) (C ε) sf) f = z • f →
      model.inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((scale : ℂ) • model.inputs.operator ε)

attribute [instance] NativePacket.strongNormed NativePacket.strongScalar NativePacket.strongComplete
  NativePacket.strongNontrivial NativePacket.weakNormed NativePacket.weakScalar
  NativePacket.weakComplete

/-- The selected-layer extension of a native packet. -/
structure NativeSelection {X Ξ Ω : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSpace Ξ] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    {K : Set X} [CompactSpace K]
    {C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain K}
    {law : ℝ≥0 → Measure Ξ} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
    {scale pressure : ℝ} (d : NativePacket K C law probability scale pressure)
    (T : X ≃ₜ X) (V G : Set X) (hK : IsCompact K)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : ℝ≥0 → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w wc : K → ℝ) (hw : Continuous w) (hwc : Measurable wc)
    (hscale : 0 < scale) (hwR : ∀ x, w x ≤ scale) (hwcR : ∀ x, wc x ≤ scale) where
  Z : Type uZ
  [zNormed : NormedAddCommGroup Z]
  [zScalar : NormedSpace ℂ Z]
  Zret : Type uZret
  [retNormed : NormedAddCommGroup Zret]
  [retScalar : NormedSpace ℂ Zret]
  Core : Type uCore
  [coreNormed : NormedAddCommGroup Core]
  [coreScalar : NormedSpace ℂ Core]
  kl : ClassicalContract (E := d.Strong) (W := d.Weak)
  det : DeterministicLeading (d.model.inputs.operator 0)
  cutoff : ℝ
  margin : ℝ
  principal_lt : d.model.inputs.principal / scale < cutoff
  cutoff_lt_rate : cutoff < det.rate
  cutoff_lt_weak : cutoff < d.model.inputs.weakRate / scale
  subordinate_lt : det.subordinate < cutoff
  margin_positive : 0 < margin
  margin_subordinate : margin < cutoff - det.subordinate
  margin_leading : margin < det.rate - cutoff
  cutoff_positive : 0 < cutoff
  rate_pressure : scale * det.rate = Real.exp pressure
  tests : Set (K →ᵇ ℝ)
  multipliers : tests → d.Strong →L[ℂ] d.Strong
  physicalSources : ∀ outputs : ProjectorOutputs d.model.inputs.operator
      (TwoNormNormalization.weakEmbedding d.inclusion) det cutoff margin,
    ∀ η : ℝ, 0 < η → ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      Nonempty (Global.NoFullSupportKLFamily.ScaleSources
        (Z := Z) (Zret := Zret) (Core := Core)
        T V K G hK (ρ ε) (F ε) (hF ε) w hw wc hwc scale hscale hwR hwcR
        outputs ε η tests multipliers)

attribute [instance] NativeSelection.zNormed NativeSelection.zScalar NativeSelection.retNormed
  NativeSelection.retScalar NativeSelection.coreNormed NativeSelection.coreScalar

local instance compactLayer {M I : Type*} [MetricSpace M] [CompactSpace M]
    (T : M ≃ₜ M) (A : Set M) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

theorem layerCompact {M I : Type*} [MetricSpace M] [CompactSpace M]
    (T : M ≃ₜ M) (A : Set M) (Λ : I → Set M) (ℓ N : ℕ) (D : AdaptedSource T A Λ ℓ)
    (i : Fin ℓ) : IsCompact (closedLayer T A Λ ℓ N D i) :=
  isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)

/-- The eventual prefix sources from native packets and one representation of the noise. -/
def assembled
    {M E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
    {ι I : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
    (F : RegularNoise.Maps (E := E) (ι := ι) T r)
    {Parameters : Type*} [MetricSpace Parameters] {evaluate : Parameters → M → M}
    (p : RegularNoise.Representation F Parameters evaluate)
    (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ)
    (smooth : RegularNoise.SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (A : Set M) (hA : IsOpen A) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (w : M → ℝ) (R : ℝ) (pressure : I → ℝ)
    (L : RegularNoise.Laws (ι := ι)) (k : ℕ) (hk : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (hw : Continuous w) (hnonnegative : ∀ x, 0 ≤ w x) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (V G B : Set M)
    (geometry : PhysicalClassicalNullPacketApplication.Geometry T A Λ ℓ N D w pressure k j G B σ)
    (live_open : IsOpen V) (live_subset : V ⊆ closedLayer T A Λ ℓ N D j)
    (retained_open : IsOpen B) (core_retained : Λ (D.index j) ⊆ B)
    (retained_live : closure B ⊆ V)
    (no_return : (T '' closure B) ∩ forwardTrapped T (closedLayer T A Λ ℓ N D j) ⊆ B)
    (core_collar : Λ (D.index j) ⊆ G)
    (cutoff : closedLayer T A Λ ℓ N D j → ℝ) (cutoff_measurable : Measurable cutoff)
    (cutoff_bound : ∀ x, cutoff x ≤ R)
    (packets : ∀ i : Fin ℓ, NativePacket (closedLayer T A Λ ℓ N D i)
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε)
        (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i)
        (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe) R hR (fun x => bound x.val))
      L.fixedLaw (fun _ => inferInstance) R (pressure (D.index i)))
    (selection : NativeSelection (packets j) T V G
      (layerCompact T A Λ ℓ N D j) L.fixedLaw
      (fun ε (z : M × RegularNoise.FixedControl (ι := ι)) => evaluate (p.fixedParameters ε z.2) z.1)
      p.allScale_measurable (fun x => w x.val) cutoff (hw.comp continuous_subtype_val)
      cutoff_measurable hR (fun x => bound x.val) cutoff_bound)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M)
    (same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, C ε =
      NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Aᶜ hA.measurableSet.compl w hw.measurable R hR bound) :
    Σ' sf : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (C ε),
      EventualScalePrefixSources.Sources (Ξ := RegularNoise.FixedControl (ι := ι))
        (Ω := RegularNoise.FixedControl (ι := ι)) (Z := selection.Z) (Zret := selection.Zret)
        (Core := selection.Core) T A hA Λ ℓ N D k hk j hjk C sf := by
  have hSF : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (C ε) := by
    filter_upwards [same, p.eventually_global_strongFeller smooth Aᶜ hA.measurableSet.compl
      w hw hnonnegative R hR bound] with ε he hs
    rw [he]
    exact hs L
  have noUp : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ i, i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
        (C ε).killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0 := by
    filter_upwards [same, p.eventually_all_shifted_kernel_support N A hA
      geometry.strict_trapping D.levels ℓ D.compact_positive D.adapted_positive
      w hw.measurable R hR bound] with ε he hn
    intro _hε i hi x hx
    rw [he]
    exact hn L i (hi.trans hk) x hx
  have zeroA : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x, (C ε).killedTransition x A = 0 := by
    filter_upwards [same] with ε he
    intro x
    rw [he]
    exact ActualAbsorbingKernelSupport.target_absorbing_mass_zero (L.fixedLaw ε)
      (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      (p.allScale_measurable ε) A hA.measurableSet w hw.measurable R hR bound x
  let densityExistence := p.exists_global_density_family L σ source Aᶜ hA.measurableSet.compl
    w hw.measurable R hR bound
  let density := Classical.choose densityExistence
  have hdensity : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
      (C ε).killedTransition x = σ.withDensity (fun y => density ε (x, y)) := by
    filter_upwards [same, (Classical.choose_spec densityExistence).2] with ε he hd
    simpa only [he] using hd
  refine ⟨hSF, ?_⟩
  exact {
    hΛ := geometry.nonempty_basic
    E := fun i => (packets i).Strong
    Mid := fun i => (packets i).Weak
    Weak := fun i => (packets i).Weak
    pressure := pressure
    hgap := geometry.pressure_gap
    iH := fun i => (packets i).inclusion
    iW := fun i => (packets i).inclusion
    law := L.fixedLaw
    prob := fun _ => inferInstance
    generator := fun i => (packets i).generator
    scale := fun _ => R
    models := fun i => (packets i).model
    essential := fun i => (packets i).essential
    kl := selection.kl
    confine := fun i => (packets i).confinement
    hdet := fun i => (packets i).radius_le
    hprincipal := fun i => (packets i).principal_le
    det := selection.det
    cutoff := selection.cutoff
    margin := selection.margin
    hαq := selection.principal_lt
    hqr := selection.cutoff_lt_rate
    hqweak := selection.cutoff_lt_weak
    hsubq := selection.subordinate_lt
    hmargin := selection.margin_positive
    hmarginSub := selection.margin_subordinate
    hmarginLead := selection.margin_leading
    hq := selection.cutoff_positive
    hpressure := selection.rate_pressure
    R := R
    hR := hR
    hscaleJ := rfl
    V := V
    G := G
    U := B
    hV := live_open
    hVK := live_subset
    hU := retained_open
    hcoreU := core_retained
    hUV := retained_live
    hUG := geometry.retained_collar
    hsep := no_return
    hcoreG := core_collar
    htrans := geometry.transitive
    w := w
    hw := hw.measurable
    hwK := hw.comp continuous_subtype_val
    hwG := geometry.weight_collar
    hwR := bound
    ρ := L.fixedLaw
    hρ := L.fixedLaw_full_support
    F := fun ε (z : M × RegularNoise.FixedControl (ι := ι)) => evaluate (p.fixedParameters ε z.2) z.1
    hF := p.allScale_measurable
    hactual := same
    hnoUp := noUp
    hzeroA := zeroA
    hUltra := fun _ => StrongFellerSquareCompact.ultraFellerContract
    hFredholm := fun _ => PowerCompactGap.squareCompactFredholm
    hcompare := NativeLayerSpectrum.eventual_layer_spectrum_of_local_spectrum
      (fun i => (packets i).Strong)
      (fun i ε => ((R : ℝ) : ℂ) • (packets i).model.inputs.operator ε)
      (fun i => (packets i).model.inputs.principal)
      L.fixedLaw
      (fun _ ε (z : M × RegularNoise.FixedControl (ι := ι)) => evaluate (p.fixedParameters ε z.2) z.1)
      (fun _ => p.allScale_measurable) Aᶜ hA.measurableSet.compl
      (fun i => closedLayer T A Λ ℓ N D i) (fun i => closedLayer_measurable T A Λ ℓ N D i)
      (LiveFiltrationRealization.closed_layer_subset_live T A Λ ℓ N D hA)
      w hw.measurable R hR bound C (fun _ => same)
      (fun i => (packets i).spectrumComparison)
    σ := ForwardNullReference.reference T σ
    density := fun ε z => ((C ε).killedTransition z.1).rnDeriv
      (ForwardNullReference.reference T σ) z.2
    hdensity := BoundaryNullDensityReference.eventually_density T σ C density hdensity
    hpre := ForwardNullReference.preimage_null T T.measurableEmbedding σ
    hnull := BoundaryNullDensityReference.positive_boundary T A Λ ℓ D σ
      geometry.shifted_boundary_null
    cutoffWeight := cutoff
    cutoff_measurable := cutoff_measurable
    cutoff_bound := cutoff_bound
    tests := selection.tests
    multipliers := selection.multipliers
    physicalSources := selection.physicalSources }

end ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
