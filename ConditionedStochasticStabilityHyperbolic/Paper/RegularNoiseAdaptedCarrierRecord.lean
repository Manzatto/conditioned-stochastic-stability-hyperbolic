module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseAdaptedCarrierStages
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierTower
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelWeakTower
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLetterBlocks
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnnealedRecord
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! D6–D8 for the actual physical carrier: the Keller–Liverani record of the
actual noisy generators on the adapted tube carrier, for the original laws on
the fixed control cube, with the compact inclusion into the weak stage
`(t-loss, s-loss)`. Its generators are the carrier operators of the literal
noise letters on the window and of the reference map outside it. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "adapted_carrier_record"

public noncomputable section
-- The section-variable linter does not finish on the final record term.
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff NNReal Topology BigOperators
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open AdaptedTubeUnitCarrierBounds

variable {E ι : Type*} {M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}
  {system : PatchSystem b}

theorem carrierRecord_rates (ρ Ln : ℝ) :
    ρ < max Ln ρ + 1 ∧ Ln ≤ max Ln ρ + 1 ∧ 1 ≤ max 1 (ρ + 1) ∧ ρ < max 1 (ρ + 1) := by
  refine ⟨?_, ?_, le_max_left _ _, lt_of_lt_of_le (lt_add_one ρ) (le_max_right _ _)⟩
  · linarith [le_max_right Ln ρ]
  · linarith [le_max_left Ln ρ]

set_option linter.style.haveILetI false in
set_option maxHeartbeats 3200000 in
theorem Maps.adapted_carrier_record (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
    {r α q : ℝ} (F : Maps (E := E) (ι := ι) T r) (positiveα : 0 < α) (subunitα : α < 1)
    (lower : α+1 < r) (αq : α < q) (hr : 1 ≤ r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (atlas : ChartAtlas system) (positiveStable : 0 < system.framing.stableDimension)
    (g : M → ℝ) (weight : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
    (radial : ConeDyadicSymbols.RadialCutoff)
    (cutoffs : ConstructedEnlargedConeSymbols.Cutoffs
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate)))
    {b₀ : ℝ} (hb₀ : 0 < b₀) (hb₀1 : b₀ < 1) (b₀q : b₀ < q)
    {t s loss : ℝ} (positiveT : 0 < t) (negativeS : s < 0) (positiveLoss : 0 < loss)
    (gap : t - s + loss < α)
    (margin : ∀ sign, BTLinkedDyadicWeights.exponent t s sign ≤ b₀)
    {lossH : ℝ} (hH : 0 < lossH) (lossT : loss < t)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : b₀ < a) (haq : a < q) (L : Laws (ι := ι)) :
    ∃ radiusT : ℝ, ∃ tubes : Finset atlas.NormalizedTubeIndex,
    ∃ d : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun i : tubes => atlas.normalizedTube radiusT i.val),
    ∃ W : Set M, ∃ openW : IsOpen W, ∃ region : W ⊆ d.capture,
    ∃ χ : M → ℝ,
    ∃ hχg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q (fun x => χ x * g x),
    ∃ support : tsupport (fun x => χ x * g x) ⊆ W,
    ∃ η : ℝ≥0, ∃ _positiveη : 0 < η,
    ∃ cap : η ≤ (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support).window,
    ∃ scale : ℝ, 1 ≤ scale ∧
    (letI := charts atlas;
     letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
     PhysicalModelAnnealedRecord.CarrierRecord
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap)
      L.fixedLaw (fun _ => inferInstance)
      (PhysicalModelWeakTower.towerInclusion
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr
        regularT forward b₀q hχg support positiveStable radial cutoffs.original
        (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrierTower.weak_norm atlas d μE openW region hb₀ hb₀1 F hr regularT forward
        b₀q hχg support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s)
        margin (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
        (carrierStage_margin margin positiveLoss.le) lossH loss loss hH positiveLoss positiveLoss
        (carrierStage_lowered t s loss) η cap))
      (MapImage.clipped (maps atlas F regularT) hr η
          (cap.trans (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
            support).below)) scale) := by
  classical
  choose radiusT tubes d W openW region χ hχg support η positiveη cap capHigh rest
    using Maps.adapted_carrier_stages μE F positiveα subunitα lower αq hr regularT forward backward
      atlas positiveStable g weight positive hg radial cutoffs hb₀ hb₀1 b₀q positiveT negativeS
      positiveLoss gap margin hH lossT ha ha1 haq
  have hM := rest.1
  have hN := rest.2.1
  choose P pressureP ρ positiveρ belowP N positiveN B hB words using rest.2.2
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  choose Lm hLm boundM using hM
  choose Ln hLn boundN using hN
  have hnorm := AdaptedTubeUnitCarrierTower.weak_norm atlas d μE openW region hb₀ hb₀1 F hr
    regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
    (carrierStage_margin margin positiveLoss.le) lossH loss loss hH positiveLoss positiveLoss
    (carrierStage_lowered t s loss) η cap
  have compactW := AdaptedTubeUnitCarrierTower.inclusionW_compact atlas d μE openW region hb₀ hb₀1
    F hr regularT forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap
  have compact := PhysicalModelWeakTower.towerInclusion_compact
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) hnorm compactW
  have compat := PhysicalModelAnalytic.intertwining
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) rfl rfl rfl rfl
    (PhysicalModelWeakTower.towerInclusion (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) hnorm)
    (PhysicalModelWeakTower.towerInclusion_core (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) hnorm) boundM boundN
  have srcM := AdaptedTubeUnitCarrierSources.sources atlas d μE openW region hb₀ hb₀1 F hr regularT
    forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent t s) margin lossH loss hH positiveLoss η cap ha ha1 hab haq
    capHigh
  have srcN := AdaptedTubeUnitCarrierSources.sources atlas d μE openW region hb₀ hb₀1 F hr regularT
    forward b₀q hχg support positiveStable radial cutoffs.original
    (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
    (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap ha ha1 hab haq
    capHigh
  have coreM := PhysicalModelAnalytic.core_continuous
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap) boundM srcM
  have coreN := PhysicalModelAnalytic.core_continuous
    (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) boundN srcN
  have hw := cap.trans (bounds atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
    support).below
  have rates := carrierRecord_rates ρ Ln
  exact ⟨radiusT, tubes, d, W, openW, region, χ, hχg, support, η, positiveη, cap, max 1 (ρ + 1),
    rates.2.2.1,
    PhysicalModelAnnealedRecord.carrierRecord_of_words
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
      (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) L.fixedLaw (fun _ => inferInstance)
      (PhysicalModelWeakTower.towerInclusion (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap)
        (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) hnorm) compact compat Lm Ln hLm hLn
      (PhysicalModelAnalytic.generatorBound (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original (BTLinkedDyadicWeights.exponent t s) margin lossH
      loss hH positiveLoss η cap) boundM hLm)
      (PhysicalModelAnalytic.generatorBound (AdaptedTubeUnitCarrier.model atlas d μE openW region hb₀ hb₀1 F hr regularT forward b₀q hχg
      support positiveStable radial cutoffs.original
      (BTLinkedDyadicWeights.exponent (t - loss) (s - loss))
      (carrierStage_margin margin positiveLoss.le) lossH loss hH positiveLoss η cap) boundN hLn)
      (MapImage.clipped (maps atlas F regularT) hr η hw)
      (MapImage.reference (maps atlas F regularT) hr η hw)
      (MapImage.clipped_zero (maps atlas F regularT) hr η hw)
      (MapImage.clipped_continuous (maps atlas F regularT) hr η hw)
      (MapImage.clipped_tendsto (maps atlas F regularT) hr η hw) coreM coreN η positiveη N
      positiveN ρ B (max Ln ρ + 1) (max 1 (ρ + 1)) positiveρ hB rates.1 rates.2.1 rates.2.2.1
      rates.2.2.2 (PhysicalModelWeakTower.towerInclusion_norm _ _ hnorm)
      (fun ε : ℝ≥0 => cube (ι := ι) ε)
      (fun ε hp hl c => letter atlas d hb₀ hb₀1 μE openW region F hr regularT forward b₀q
        hχg support η cap ε hp hl c) (fun ε hp z => NoiseCubeRescaling.rescale (ε : ℝ) hp z)
      ⟨0, MapImage.zero_mem_cube η⟩
      (fun ε hp hl z => MapImage.clipped_pos (maps atlas F regularT) hr η hw hp hl z)
      (fun z => (MapImage.clipped_zero (maps atlas F regularT) hr η hw z).trans
        (MapImage.reference_eq_noise (maps atlas F regularT) hr η hw positiveη)) words⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
