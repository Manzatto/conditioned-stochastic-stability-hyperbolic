module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderProvedNoiseSources
meta import Lean.LibrarySuggestions.Basic

/-! The proved ordinary noise sources of the adapted tube carrier: its core
actions depend continuously on the letter (interpolation through the higher
ordinary window of order `a`). -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierSources"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierSources
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
  {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : b < a) (haq : a < q)
  (capHigh : η ≤ (bounds atlas d μE openV region ha ha1 F hr regularT hT haq hg support).window)

/-- The proved noise sources of the carrier. -/
def sources :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalManifoldNoiseSources.Data (AdaptedTubeUnitCarrier.model atlas d μE openV region hb hb1
      F hr regularT hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW
      η cap) := by
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact ConstructedHolderProvedNoiseSources.data μE (fun j => atlas.normalizedTubeChart j)
    (localization atlas d) (tubeChart_mem atlas) openV region hb hb1 (maps atlas F regularT) hr
    (smoothT atlas hT) hbq (hg.scalarLinearRechart atlas.originalModelEquiv) support η cap
    (volume : Measure (Leaf system)) (unitSlope system positiveStable)
    (fun _ => unitLeaves system positiveStable)
    (fun _ => ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (fun _ => ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate))
    (fun _ => radial) (fun _ => angle) (fun _ => exponent) (fun _ => margin)
    (fun _ => lossH) (fun _ => lossW) (fun _ => hH) (fun _ => hW)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ha ha1 hab haq capHigh

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierSources
