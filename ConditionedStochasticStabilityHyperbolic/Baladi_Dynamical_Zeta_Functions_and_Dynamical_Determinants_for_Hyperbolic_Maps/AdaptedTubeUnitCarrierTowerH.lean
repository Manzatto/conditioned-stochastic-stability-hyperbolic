module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierTower
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTowerFacts
meta import Lean.LibrarySuggestions.Basic

/-! The intermediate stage of the adapted tube carrier: its intermediate
blocks are the core blocks with exponents lowered by the intermediate loss, so
the strong carrier's intermediate completion is isometric to the strong
completion of the carrier with those lowered exponents, and the intermediate
inclusion is compact. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierTowerH"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierTowerH
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
  (lossH lossW : ℝ) (hH : 0 < lossH) (hW : 0 < lossW)
  (η : NNReal) (cap : η ≤ (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).window)

local notation "carrier" => model atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
  positiveStable radial angle exponent margin lossH lossW hH hW η cap

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- The carrier's intermediate local block norm is the core block norm with
exponents lowered by the intermediate loss. -/
theorem hBlocks_norm (i) (f) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(carrier).weakLocalBlocksH i f‖ =
    ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) hb hb1 (fun a => exponent a - lossH)
      (fun a => (sub_le_self _ hH.le).trans (margin a)) () f‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  have compactK := ConstructedManifoldLocalization.support_compact
    (fun j => atlas.normalizedTubeChart j) (localization atlas d) i.val
  have lowered : ∀ a, exponent a - (lossH + 0) ≤ b := fun a => by
    linarith [margin a, hH]
  have key := SchwartzAmbientWeakBlocks.weak_coreMap_norm (volume : Measure (Leaf system))
    (unitSlope system positiveStable) (unitLeaves system positiveStable) _
    (ConeDyadicSymbols.symbols radial angle) exponent
    (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 exponent margin ()) lossH hH (fun _ => 0) (fun _ => le_rfl)
    (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 _ lowered ()) f
  refine key.trans ?_
  exact coreBlocks_norm_congr hb hb1 positiveStable radial angle compactK
    (funext fun a => by ring) lowered _ f

/-- The carrier's intermediate inclusion is compact. -/
theorem inclusionH_compact :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    IsCompactOperator (carrier).inclusionH := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact PhysicalModelTowerFacts.inclusionH_isCompact (carrier) fun i =>
    AdaptedTubeUnitCarrierCompact.local_compact positiveStable hb hb1 radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) exponent margin hH

variable (exponentH : Bool → ℝ) (marginH : ∀ a, exponentH a ≤ b)
  (lossH' lossW' : ℝ) (hH' : 0 < lossH') (hW' : 0 < lossW')
  (lowered : exponentH = fun a => exponent a - lossH)

local notation "middle" => model atlas d μE openV region hb hb1 F hr regularT
  hT hbq hg support positiveStable radial angle exponentH marginH lossH' lossW' hH' hW' η cap

include lowered in
/-- Chartwise, the carrier's intermediate blocks have the middle carrier's norms. -/
theorem chart_norm (i) (f) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(carrier).weakLocalBlocksH i f‖ = ‖(middle).localBlocks i f‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  refine (hBlocks_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap i f).trans ?_
  exact coreBlocks_norm_congr hb hb1 positiveStable radial angle _ lowered.symm _ marginH f

include lowered in
theorem middle_norm (c) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(carrier).qH c‖ = ‖(middle).qa c‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact (chart_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable
      radial angle exponent margin lossH lossW hH hW η cap exponentH marginH lossH' lossW' hH' hW'
      lowered i _).le.trans (norm_le_pi_norm ((middle).qa c) i)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact (chart_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable
      radial angle exponent margin lossH lossW hH hW η cap exponentH marginH lossH' lossW' hH' hW'
      lowered i _).ge.trans (norm_le_pi_norm ((carrier).qH c) i)

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierTowerH
