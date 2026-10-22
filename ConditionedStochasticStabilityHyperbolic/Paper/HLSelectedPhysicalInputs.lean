module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLeadingTrace
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalStability

/-! A single record of ordinary inputs on abstract physical models and an
abstract weak space. The actual canonical model is substituted once by the
final application. No completed annealed estimates, noisy spectral output, product
probability or convergence conclusion is assumed in this record. -/
public noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX uCarrier

structure Data
  {Carrier : Type uCarrier}
  {M : Type uX} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (ms mh : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space (u) holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (hΛ : isolatedCore T K = Λ) (hΛK : Λ ⊆ K)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {ι : Type*} [Fintype ι]
  (N : RegularNoise.Maps (E := E) (ι := ι) T h.r)
  (L : RegularNoise.Laws (ι := ι))
  (representation : RegularNoise.Representation N Ω mh.maps)
  (w : K → ℝ) (R : ℝ) (hR : 0 < R)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure] where
  G : Set M
  B : Set M
  equilibrium : HyperbolicBasicSet.EquilibriumPackage h.basic.hyperbolic g
  φ : M → ℝ
  hφ : ∀ x ∈ Λ, g x = Real.exp (φ x)
  hF : ∀ ε : ℝ≥0, Measurable (fun z : M × RegularNoise.FixedControl (ι := ι) =>
      ((mh)).maps ((representation).fixedParameters ε z.2) z.1)
  hw : Continuous w
  hwG : ∀ x : K, x.val ∈ G → 0 < w x
  wc : K → ℝ
  hwc : Measurable wc
  hwR : ∀ x : K, w x ≤ R
  hwcR : ∀ x, wc x ≤ R
  hweight : ∀ x : K, ((mh)).weight x.val = wc x
  commonS : PhysicalHolderClassicalSources.Data (u) holder (ms) K (σ.comap Subtype.val)
  common : PhysicalHolderClassicalSources.Data (u) holder (mh) K (σ.comap Subtype.val)
  ordinarySource : RegularLayerNoiseSources.Data representation σ V K G B (hK) w wc R
      (fullView (u) holder) (fullView_injective (u) holder) (fullCore (u) holder)
  submersion : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ
  hBG : closure B ⊆ G
  r : ℝ
  t : ℝ
  sn : ℝ
  margins : RegularCoreApproximation.RegularityMargins r t sn u
  rowsS : PhysicalManifoldRowSources.Data ms
  rowsH : PhysicalManifoldRowSources.Data mh
  noiseH : PhysicalManifoldNoiseSources.Data mh
  essential : ∀ {Z : Type uCarrier} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
      [CompleteSpace Z], EssentialRadiusContract (E := Z) (W := W)
  kl : ∀ {Z : Type uCarrier} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
      [CompleteSpace Z], ClassicalContract (E := Z) (W := W)
  dsRaw : PhysicalManifoldModel.Data.GeneratorLeading (ms) representation.reference
  dmRaw : PhysicalManifoldModel.Data.GeneratorLeading (mh) representation.reference
  rateS : dsRaw.rate = Real.exp equilibrium.pressure
  rateH : dmRaw.rate = Real.exp equilibrium.pressure
  realCutoffS : ∀ a x, conj (((ms)).localization.cutoff a x) = ((ms)).localization.cutoff a x
  realCutoffH : ∀ a x, conj (((mh)).localization.cutoff a x) = ((mh)).localization.cutoff a x
  evenAngleS : ∀ a ξ, (((ms)).angle a).toFun (-ξ) = (((ms)).angle a).toFun ξ
  evenAngleH : ∀ a ξ, (((mh)).angle a).toFun (-ξ) = (((mh)).angle a).toFun ξ
  a2 : ∀ {H : Type uCarrier} {P Z Reg : Type uX}
      [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
      [NormedAddCommGroup Z] [NormedSpace ℂ Z]
      [NormedAddCommGroup Reg] [NormedSpace ℂ Reg],
      CommonAmbientClassicalComparison.ClassicalContract
        (A := H) (F := P) (Z := Z) (Reg := Reg) (W := W)
  deterministicEquilibrium : ∀ ψ : SmoothPhysicalTests.tests (E := E) K,
      (∫ x, ψ.val x ∂(h.stateOnCollar equilibrium K ((hK)).measurableSet
        hΛK : Measure K)) =
      PhysicalManifoldModel.Data.GeneratorLeading.multiplierTrace mh dmRaw
        (SmoothSupportedManifoldCore.multiplier V (SmoothPhysicalTests.complexExtension K ψ)
          (SmoothPhysicalTests.complexExtension_smooth K ψ))



end ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
