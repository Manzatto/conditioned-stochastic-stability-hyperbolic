module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderAnnealedConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalLayerUniversalScaleFactory
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! Ordinary cited anisotropic facts over the actual supported/full little
Hölder spaces. All regular realizations, dense cores, test inclusions and
physical compatibility identities are constructed, not source fields. -/

public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 100000
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
open LeanShared DyadicCompletion SmoothSupportedManifoldCore

universe uM
variable {M : Type uM} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)



variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]


open KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
variable [MetricSpace Ω]


variable {ι : Type*} [Fintype ι] {T : M ≃ₜ M} {rNoise : ℝ}
    (F : RegularNoise.Maps (E := E) (ι := ι) T rNoise)
    (p : RegularNoise.Representation F Ω m.maps)
    {Fiber : M → Type*} [∀ x, NormedAddCommGroup (Fiber x)]
    [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
    {Params : Type*} {I : ℕ → Type*} {Order : Type*} [Fintype Order]
    (G B : Set M) (hK : IsCompact K) (w wc : K → ℝ) (R : ℝ)


namespace Data
variable (d : Data u holder m K σ F p (Fiber := Fiber) (Params := Params) (I := I)
  (Order := Order) G B hK w wc R)

/- Actual KL projectors and ordinary geometric sources produce every
physical comparison, positive-density and supported smooth-core premise
needed by the selected layer's quasi-ergodic theorem. -/
-- Preserve the inferred canonical parent dictionaries of the constructed source.
set_option linter.defProp false in
def scale_sources (L : RegularNoise.Laws (ι := ι))
    (essential : EssentialRadiusContract (E := m.StrongSpace)
      (W := closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)))
    {det : DeterministicLeading ((d.model u holder m K σ F p G B hK w wc R L).model.inputs.operator 0)}
    {q δ : ℝ}
    (outputs : ProjectorOutputs (d.model u holder m K σ F p G B hK w wc R L).model.inputs.operator
      (TwoNormNormalization.weakEmbedding
        (m.loweredInclusion m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)) det q δ)
    (hδsub : δ < q - det.subordinate) (hδlead : δ < det.rate - q) (hq : 0 < q)
    (hprincipal : (d.model u holder m K σ F p G B hK w wc R L).model.inputs.principal / R < q)
    (classical : ∀ {Z : Type uM} [NormedAddCommGroup Z] [NormedSpace ℂ Z],
      CommonAmbientClassicalComparison.ClassicalContract (A := m.StrongSpace)
      (F := SupportedPairingClosedCore.space (physicalRealization V K m.regularCore))
      (Z := Z) (Reg := Regular u holder V)
      (W := closedCore (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative))) :=
  PhysicalLayerUniversalScaleFactory.eventual_sources u holder m K (σ.comap Subtype.val)
    d.primitive.rows d.primitive.noiseRegularity L.fixedLaw p.fixedParameters p.fixedParameters_continuous
    (m.loweredInclusion m.lossW m.lossW_positive m.extraW m.extraW_nonnegative) R
    (d.model u holder m K σ F p G B hK w wc R L).model.inputs
    (d.model u holder m K σ F p G B hK w wc R L).model.generator_eq T G B hK
    p.allScale_measurable w d.weight_continuous wc d.cutoff_measurable
    (zero_lt_one.trans_le d.scale_ge_one) d.weight_bound d.cutoff_bound d.model_weight d.common
    (d.noiseSources u holder m K σ F p G B hK w wc R L) d.regularR d.regularT d.regularS d.margins
    essential (d.model u holder m K σ F p G B hK w wc R L).model.injectiveW
    (d.model u holder m K σ F p G B hK w wc R L).model.compactW
    outputs hδsub hδlead hq hprincipal d.realCutoff d.evenAngle classical

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
