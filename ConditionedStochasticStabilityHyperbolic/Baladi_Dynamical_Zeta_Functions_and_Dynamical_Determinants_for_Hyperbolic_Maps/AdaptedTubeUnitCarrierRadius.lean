module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusFrom
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierPairing
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelSubordinateRadius
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelFullTestDistribution
public import LeanShared.Dynamics.HyperbolicLinearRechartPotential
public import LeanShared.Dynamics.HyperbolicLinearRechartPeriodic
public import LeanShared.Dynamics.BasicHyperbolicRestrictNeighborhood
public import LeanShared.Geometry.FractionalLinearRechartRegularity
public import LeanShared.Geometry.FractionalScalarLinearRechart
public import LeanShared.Geometry.HigherFractionalLowerRegularity
meta import Lean.LibrarySuggestions.Basic

/-! Upper bound of the deterministic spectral radius of the adapted tube carrier at the pressure.
With the transported tangent metric, the transported basic set restricted to the carrier region,
the order-one Hölder test distribution and the compact two-norm estimate of the deterministic
generator, the radius is at most `e^P`. No mixing, forward support, leading record or trace data
is used. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierRadius"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierRadius
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open AllFakeLeafModel AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
open LinearRechartedManifold HyperbolicLinearRechart FractionalManifoldRegularity ThermodynamicDefinitions
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
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

set_option maxHeartbeats 3200000 in
theorem carrier_radius_upper (ht : ∀ s, 0 < 1 + exponent s)
    (backward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (T.symm : M → M))
    (weightNonneg : ∀ x, 0 ≤ g x) (weightPos : ∀ x ∈ Λ, 0 < g x) (withinV : closure V ⊆ V₀)
    (P0 : ℝ) (hP0 : pressure T (base.hyperbolic.potential g) Λ = (P0 : EReal)) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ (a : _) (_hTa : (carrier).maps a = T) {L : ℝ}
      (_bound : PhysicalModelAnalytic.AnalyticBound (carrier) L)
      {W : Type*} {_iW : NormedAddCommGroup W} {_sW : NormedSpace ℂ W},
      PhysicalModelNativeRadiusUpper.RadiusFrom (carrier) a P0 W := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro a hTa L bound W _ _
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let _ : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, system.EuclideanModel)) x) :=
    ⟨transportMetric atlas.originalModelEquiv original⟩
  let _ := continuous_metric (M := M) atlas.originalModelEquiv
  have coreV : Λ ⊆ V := fun x hx => support (subset_tsupport _ (weightPos x hx).ne')
  let transported := transportBasic atlas.originalModelEquiv base (hT.mdifferentiable one_ne_zero)
    (backward.mdifferentiable one_ne_zero)
  let bd := transported.restrictNeighborhood V openV coreV (fun x hx => withinV (subset_closure hx))
  have samePotential : bd.hyperbolic.potential g = base.hyperbolic.potential g :=
    basic_potential_eq atlas.originalModelEquiv base (hT.mdifferentiable one_ne_zero)
      (backward.mdifferentiable one_ne_zero) g
  have pressure' : pressure T (bd.hyperbolic.potential g) Λ = (P0 : EReal) := samePotential ▸ hP0
  let refData : FiniteSmoothReferenceCharts.Data (E := system.EuclideanModel) (M := M) :=
    Classical.choice FiniteSmoothReferenceCharts.exists_data
  have localBound := AdaptedTubeUnitCarrierPairing.localPairing atlas d μE openV region hb hb1 F hr
    regularT hT hbq hg support positiveStable radial angle exponent margin lossH lossW hH hW η cap
    one_pos le_rfl ht
  have key := PhysicalModelNativeRadiusUpper.native_radius_upper (carrier) bound a bd hTa.symm
    (contMDiff_one_rechart atlas.originalModelEquiv hT)
    (contMDiff_one_rechart atlas.originalModelEquiv backward)
    (hg.differentiable.continuous) weightNonneg weightPos
    (fun x hx => subset_closure (support (subset_tsupport _ hx))) refData P0 pressure' localBound
    (ManifoldSmoothHolderCore.physical (fun j => atlas.normalizedTubeChart j) (localization atlas d)
      openV hb hb1) (fun _ _ => rfl) (W := W)
  exact key

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierRadius
