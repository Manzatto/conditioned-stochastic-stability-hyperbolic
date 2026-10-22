module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierCompact
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalytic
meta import Lean.LibrarySuggestions.Basic

/-! The weak stage of the adapted tube carrier is the carrier with lowered
exponents. The strong carrier's weak completion is isometric to the weak
carrier's strong completion, which gives a compact inclusion `j` that is the
identity on the common smooth core. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierTower"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierTower
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open DyadicCompletion
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base}
  (atlas : ChartAtlas system) {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : tubes => atlas.normalizedTube radius i.val))
  (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
  {V : Set M} (openV : IsOpen V) (region : V ⊆ d.capture)
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  {r : ℝ} (F : Paper.RegularNoise.Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
  (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (hT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g : M → ℝ} {q : ℝ} (hbq : b < q)
  (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
  (support : tsupport g ⊆ V)
  (positiveStable : 0 < system.framing.stableDimension)
  (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate)))
  (exponent : Bool → ℝ) (margin : ∀ a, exponent a ≤ b)
  (exponentW : Bool → ℝ) (marginW : ∀ a, exponentW a ≤ b)
  (lossH lossW lossW' : ℝ) (hH : 0 < lossH) (hW : 0 < lossW) (hW' : 0 < lossW')
  (lowered : exponentW = fun a => exponent a - lossW)
  (η : NNReal) (cap : η ≤ (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).window)

local notation "strong" => AdaptedTubeUnitCarrier.model atlas d μE openV region hb hb1 F hr regularT
  hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap
local notation "weak" => AdaptedTubeUnitCarrier.model atlas d μE openV region hb hb1 F hr regularT
  hT hbq hg support positiveStable radial angle exponentW marginW lossH lossW' hH hW' η cap

/-- The strong carrier's weak inclusion is compact. -/
theorem inclusionW_compact :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    IsCompactOperator (strong).inclusionW := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact PhysicalModelCompactWeak.inclusionW_isCompact (strong) fun i =>
    AdaptedTubeUnitCarrierCompact.local_compact positiveStable hb hb1 radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) exponent margin hW

include lowered in
/-- Chartwise, the strong carrier's weak blocks have the weak carrier's norms. -/
theorem chart_norm (i) (f) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(strong).weakLocalBlocksW i f‖ = ‖(weak).localBlocks i f‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  refine (weakBlocks_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap i f).trans ?_
  exact coreBlocks_norm_congr hb hb1 positiveStable radial angle _ lowered.symm _ marginW f

include lowered in
theorem weak_norm (c) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(strong).qW c‖ = ‖(weak).qa c‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact (chart_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable
      radial angle exponent margin exponentW marginW lossH lossW lossW' hH hW hW' lowered η cap i
      _).le.trans (norm_le_pi_norm ((weak).qa c) i)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact (chart_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable
      radial angle exponent margin exponentW marginW lossH lossW lossW' hH hW hW' lowered η cap i
      _).ge.trans (norm_le_pi_norm ((strong).qW c) i)

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierTower
