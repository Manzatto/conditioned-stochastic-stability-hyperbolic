module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrier
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelRealStructure
public import LeanShared.Geometry.ManifoldHolderQuotientConjugation
meta import Lean.LibrarySuggestions.Basic

/-! Real structure of the adapted tube carrier: its localization cutoffs are
real, its angular symbol is even whenever the chosen angular cutoff is, and
pointwise conjugation of the ordinary lower-regularity space realizes complex
conjugation of the physical functions. These are the inputs of
`PhysicalModelRealStructure.actualConjugation`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierReal"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierReal
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open KellerLiverani1999
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

theorem cutoff_real (i) (x : M) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    conj ((carrier).localization.cutoff i x) = (carrier).localization.cutoff i x := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  change conj ((d.beta i.val x : ℝ) : ℂ) = ((d.beta i.val x : ℝ) : ℂ)
  exact Complex.conj_ofReal _

theorem angle_even (hangle : ∀ ξ, angle.toFun (-ξ) = angle.toFun ξ) (i) (ξ) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ((carrier).angle i).toFun (-ξ) = ((carrier).angle i).toFun ξ :=
  hangle ξ

/-- Pointwise conjugation on the carrier's ordinary regular space. -/
def jreg :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ConstructedHolderPhysicalModel.Regular (fun j => atlas.normalizedTubeChart j)
      (localization atlas d) openV hb hb1 →L[ℝ]
    ConstructedHolderPhysicalModel.Regular (fun j => atlas.normalizedTubeChart j)
      (localization atlas d) openV hb hb1 := by
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact ManifoldHolderQuotient.conjugate (ManifoldSmoothHolderCore.regions
    (fun j => atlas.normalizedTubeChart j) (localization atlas d) openV) hb hb1

theorem view_jreg (v) (x : M) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    (carrier).view (jreg atlas d openV hb hb1 v) x = star ((carrier).view v x) := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  exact ManifoldHolderQuotient.physical_conjugate _ hb hb1 v x

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierReal
