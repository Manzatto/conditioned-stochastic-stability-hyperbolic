module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafLeafTranslation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelAnalyticMultiplier
meta import Lean.LibrarySuggestions.Basic

/-! Bounded multiplication by smooth global functions on the strong space of the adapted tube
carrier: its shared fake-leaf family is translation-closed, so the generic manifold multiplier
bound applies whenever the exponents satisfy the first-commutator conditions. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierMultiplier"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierMultiplier
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

/-- Multiplication by a smooth global function is bounded on the carrier's strong core norm. -/
theorem analyticMultiplier (h1 : ∀ σ s, exponent σ - 1 - exponent s < 0)
    (h2 : ∀ s, -1 - exponent s < 0) (h3 : ∀ σ, exponent σ ≤ 1) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ (ψ : M → ℂ) (hψ : ContMDiff (𝓘(ℝ, system.EuclideanModel)) (𝓘(ℝ, ℂ)) ∞ ψ),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ c : PhysicalManifoldModel.Core (E := system.EuclideanModel) V,
        ‖DyadicCompletion.coreLift (carrier).qa (SmoothSupportedManifoldCore.multiplier V ψ hψ c)‖ ≤
          C * ‖DyadicCompletion.coreLift (carrier).qa c‖ :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  fun ψ hψ => PhysicalModelAnalyticMultiplier.analytic_multiplier (carrier)
    (fun _ c z => AllFakeLeafLeafTranslation.translate (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) () c z)
    (fun _ => h1) (fun _ => h2) (fun _ => h3) ψ hψ

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierMultiplier
