module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily

/-! The eventual physical source packet depends on the noise law and the noisy map only through
their values: equal laws and equal maps give the same packet. This transports a source packet
produced for a carrier's literal clipped representation to the globally fixed physical family on
the scales where the two coincide. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
open LeanShared KellerLiverani1999

variable {H Vweak Z Zret Core X Ω : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Vweak] [NormedSpace ℂ Vweak]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

omit [CompleteSpace H] [CompactSpace X] [SecondCountableTopology X] [CompactSpace Ω] in
/-- Scale sources are invariant under equal noise laws and equal noisy maps. -/
theorem ScaleSources.congr (T : X ≃ₜ X) (V K G : Set X) (hK : IsCompact K) [CompactSpace K]
    {noise noise' : Measure Ω} [IsProbabilityMeasure noise] [IsProbabilityMeasure noise']
    {F F' : X × Ω → X} (hF : Measurable F) (hF' : Measurable F')
    (w : K → ℝ) (hw : Continuous w) (wc : K → ℝ) (hwc : Measurable wc)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (hwcR : ∀ x, wc x ≤ R)
    {P : ℝ≥0 → H →L[ℂ] H} {weak : H →L[ℂ] Vweak}
    {det : DeterministicLeading (P 0)} {q δ : ℝ}
    (o : ProjectorOutputs P weak det q δ) (ε : ℝ≥0) (η : ℝ)
    (A : Set (K →ᵇ ℝ)) (M : A → H →L[ℂ] H)
    (hnoise : noise = noise') (hmap : F = F')
    (s : Nonempty (ScaleSources (Z := Z) (Zret := Zret) (Core := Core) T V K G hK noise F hF
      w hw wc hwc R hR hwR hwcR o ε η A M)) :
    Nonempty (ScaleSources (Z := Z) (Zret := Zret) (Core := Core) T V K G hK noise' F' hF'
      w hw wc hwc R hR hwR hwcR o ε η A M) := by
  subst hnoise
  subst hmap
  exact s

end ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
