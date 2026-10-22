module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierMultiplier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelBumpVectors
meta import Lean.LibrarySuggestions.Basic

/-! The block norm calculus of the adapted tube carrier: its shared complete fake-leaf family is
translation closed, its blocks are bounded on every compact support, and Schwartz multipliers
are bounded under the first-commutator exponent conditions. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierCalculus"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierCalculus
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

theorem localCalculus (h1 : ∀ σ s, exponent σ - 1 - exponent s < 0)
    (h2 : ∀ s, -1 - exponent s < 0) (h3 : ∀ σ, exponent σ ≤ 1) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    PhysicalModelBumpVectors.LocalCalculus (carrier) :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  { sfinite := fun _ _ => PhysicalModelAnalyticMultiplier.leaf_sFinite _
    translate := fun _ c z => AllFakeLeafLeafTranslation.translate (unitPlanes system)
      (unitPlus system) (unitCone system positiveStable) (unitCoordinates system)
      (unitBasis system) () c z
    bounded := fun _ _ hK => AllFakeLeafHolderCoreBounds.bounded (unitPlanes system)
      (unitPlus system) (unitCone system positiveStable) (unitCoordinates system)
      (unitBasis system) radial angle hK hb hb1 exponent margin ()
    multiplier := fun j a K hK =>
      let bound := ConeMultiplierBound.multiplier_bound volume (carrier).slope_nonnegative
        ((carrier).leaves j) K ((carrier).radial j) ((carrier).angle j) ((carrier).exponent j)
        (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
          (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
          hK hb hb1 exponent margin ())
        (fun c z => AllFakeLeafLeafTranslation.translate (unitPlanes system) (unitPlus system)
          (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) () c z)
        h1 h2 h3 a
      ⟨bound.choose, bound.choose_spec.2⟩ }

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierCalculus
