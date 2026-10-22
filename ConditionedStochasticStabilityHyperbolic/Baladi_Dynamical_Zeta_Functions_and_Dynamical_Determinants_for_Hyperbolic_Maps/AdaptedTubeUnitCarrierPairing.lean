module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafLowOrderPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestPairing
meta import Lean.LibrarySuggestions.Basic

/-! The adapted tube carrier has the local low-order pairing property for Hölder tests of every
order `bt ∈ (0,1]` with `bt + t(s) > 0`: its local norms are the complete fake-leaf block norms.
-/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierPairing"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierPairing
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
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

theorem chart_bound (i : letI := charts atlas;
      letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
      (carrier).localization.indices)
    {K : Set system.EuclideanModel} (hK : IsCompact K) {bt : ℝ}
    (hbt : 0 < bt) (hbt1 : bt ≤ 1) (ht : ∀ s, 0 < bt + exponent s) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support (carrier).atlas (carrier).localization i))
      (v : BoundedHolderSpace.graph system.EuclideanModel bt),
      tsupport (BoundedHolderSpace.physical system.EuclideanModel bt v) ⊆ K →
      ‖∫ x, g.val x * BoundedHolderSpace.physical system.EuclideanModel bt v x‖ ≤ C * ‖v‖ *
        ‖(carrier).localBlocks i g‖ :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  AllFakeLeafLowOrderPairing.chart_pairing (unitPlanes system)
    (unitPlus system) (unitCone system positiveStable) (unitCoordinates system) (unitBasis system)
    radial angle (ConstructedManifoldLocalization.support_compact
      (fun j => atlas.normalizedTubeChart j) (localization atlas d) i.val) hb hb1 exponent margin ()
    hK hbt hbt1 ht

theorem localPairing {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (ht : ∀ s, 0 < bt + exponent s) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalModelFullTestPairing.LocalPairing (carrier) bt := fun i _ hK =>
  chart_bound atlas d μE openV region hb hb1 F hr regularT hT hbq hg support positiveStable radial
    angle exponent margin lossH lossW hH hW η cap i hK hbt hbt1 ht

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierPairing
