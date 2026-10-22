module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeCarrierModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafNativeInputBounds
public import LeanShared.Analysis.SchwartzAmbientWeakBlocks

meta import Lean.LibrarySuggestions.Basic
/-! The physical carrier on the adapted tube atlas with ONE fake-leaf family
shared by every chart (leaf-chart index type `Unit`). Every chart therefore
uses literally the same leaves, symbols and exponents, so the input and
output norms of the polarized chart-pair bound (stated with one leaf index
`o`) are the carrier's own local norms in every chart pair. -/
-- The theorem statements below contain the whole carrier; exclude them from
-- the library-suggestion symbol-frequency export, which does not share subterms.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrier"

@[expose] public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrier
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.OrthogonalProductCoordinates AllFakeLeafModel
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base}

/-- Unit-indexed constant fake-leaf data. -/
abbrev unitPlanes (system : PatchSystem base) : Unit → Submodule ℝ system.EuclideanModel :=
  fun _ => firstPlane system.euclideanDimension
abbrev unitPlus (system : PatchSystem base) : Unit → Set system.EuclideanModel :=
  fun _ => ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem unitCone (system : PatchSystem base) (positiveStable : 0 < system.framing.stableDimension) :
    ∀ o, ConeData (unitPlanes system o) (unitPlus system o) :=
  fun _ => AdaptedHalfConeData.halfConeData system.euclideanDimension
    (by rw [finrank_euclideanSpace_fin]; exact positiveStable)

abbrev unitBasis (system : PatchSystem base) :
    ∀ o, OrthonormalBasis (Fin system.framing.unstableDimension) ℝ (unitPlanes system o) :=
  fun _ => leafBasis system
abbrev unitCoordinates (system : PatchSystem base) :
    ∀ o, Leaf system ≃ₗᵢ[ℝ] unitPlanes system o :=
  fun _ => (leafBasis system).repr.symm

/-- The one shared leaf family. -/
abbrev unitLeaves (system : PatchSystem base) (positiveStable : 0 < system.framing.stableDimension) :=
  AllFakeLeafHolderCoreBounds.leaves (unitPlanes system) (unitPlus system)
    (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) ()

abbrev unitSlope (system : PatchSystem base) (positiveStable : 0 < system.framing.stableDimension) :=
  GraphJacobian.densityBound_nonneg (ι := Fin system.framing.unstableDimension)
    (Heterogeneous.commonSlope (unitPlanes system) (unitPlus system) (unitCone system positiveStable))

variable (atlas : ChartAtlas system) {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
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

/-- The physical carrier on the adapted tube atlas with one shared leaf family,
constant exponents, constant losses and no extra branch weakening. -/
def model :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  ConstructedHolderNoiseImageModel.model μE (fun j => atlas.normalizedTubeChart j)
    (localization atlas d) (tubeChart_mem atlas) openV region hb hb1
    (maps atlas F regularT) hr (smoothT atlas hT) hbq
    (hg.scalarLinearRechart atlas.originalModelEquiv) support η cap
    (volume : Measure (Leaf system)) (unitSlope system positiveStable)
    (fun _ => unitLeaves system positiveStable)
    (fun _ => ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (fun _ => ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate))
    (fun _ => radial) (fun _ => angle) (fun _ => exponent) (fun _ => margin)
    (fun _ => lossH) (fun _ => lossW) (fun _ => hH) (fun _ => hW)
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

local notation "carrier" => model atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
  positiveStable radial angle exponent margin lossH lossW hH hW η cap

omit [FiniteDimensional ℝ E] in
/-- The carrier's local blocks are the polarized chart-pair core blocks
(leaf index `()`). -/
theorem localBlocks_eq (i) (f) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    (carrier).localBlocks i f =
    AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) hb hb1 exponent margin () f :=
  rfl

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- The carrier's local realization is the compact Hölder realization of the
polarized chart-pair bound (leaf index `()`). -/
theorem localRealize_eq (i) (x) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    CompletedChartPairTransfer.localRealize (carrier).atlas (carrier).localization
      (carrier).localCore (carrier).localBlocks i x =
    CompactHolderPhysicalBlocks.realize (volume : Measure (Leaf system))
      (unitSlope system positiveStable) (unitLeaves system positiveStable) radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) hb hb1 exponent margin x :=
  rfl

omit [FiniteDimensional ℝ E] [CompactSpace M] in
/-- Core blocks with equal exponent functions have equal norms. -/
theorem coreBlocks_norm_congr {K : Set system.EuclideanModel} (compactK : IsCompact K)
    {t t' : Bool → ℝ} (same : t = t') (ht : ∀ a, t a ≤ b) (ht' : ∀ a, t' a ≤ b)
    (f : SchwartzJetSpace.supportedCore K) :
    ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 t ht () f‖ =
    ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 t' ht' () f‖ := by
  subst same
  rfl

omit [FiniteDimensional ℝ E] in
set_option backward.isDefEq.respectTransparency false in
/-- The carrier's weak local block norm is the polarized chart-pair weak
norm: exponents lowered by the weak loss. -/
theorem weakBlocks_norm (i) (f) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ‖(carrier).weakLocalBlocksW i f‖ =
    ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      (ConstructedManifoldLocalization.support_compact (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) i.val) hb hb1 (fun a => exponent a - lossW)
      (fun a => (sub_le_self _ hW.le).trans (margin a)) () f‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  have compactK := ConstructedManifoldLocalization.support_compact
    (fun j => atlas.normalizedTubeChart j) (localization atlas d) i.val
  have lowered : ∀ a, exponent a - (lossW + 0) ≤ b := fun a => by
    linarith [margin a, hW]
  have key := SchwartzAmbientWeakBlocks.weak_coreMap_norm (volume : Measure (Leaf system))
    (unitSlope system positiveStable) (unitLeaves system positiveStable) _
    (ConeDyadicSymbols.symbols radial angle) exponent
    (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 exponent margin ()) lossW hW (fun _ => 0) (fun _ => le_rfl)
    (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 _ lowered ()) f
  refine key.trans ?_
  exact coreBlocks_norm_congr hb hb1 positiveStable radial angle compactK
    (funext fun a => by ring) lowered _ f

omit [FiniteDimensional ℝ E] in
/-- The carrier's local view is the physical evaluation of the closed local space. -/
theorem localView_apply (i : letI := charts atlas;
      letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
      (carrier).localization.indices)
    (output : letI := charts atlas; EuclideanSmoothHolderCore.space
      (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
        (localization atlas d) i.val).closure hb hb1) (z : system.EuclideanModel) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    (carrier).localView i output z = EuclideanSmoothHolderCore.physical
      (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
        (localization atlas d) i.val).closure hb hb1 output z := rfl

omit [FiniteDimensional ℝ E] in
/-- A closed local output whose physical values are the literal chart-pair
transfer is the carrier's local pair. -/
theorem localPair_eq (Fw : M → M) (gw : M → ℝ)
    (pairMember : letI := charts atlas;
      letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
      ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support (carrier).atlas (carrier).localization j)),
      ChartPairTransfer.pair ((carrier).atlas i) ((carrier).atlas j)
        ((carrier).localization.cutoff i) Fw gw f.val ∈ ((carrier).localView i).range)
    (i j : letI := charts atlas;
      letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
      (carrier).localization.indices)
    (f : letI := charts atlas; SchwartzJetSpace.supportedCore
      (ConstructedManifoldLocalization.support (fun j => atlas.normalizedTubeChart j)
        (localization atlas d) j.val))
    (output : letI := charts atlas; EuclideanSmoothHolderCore.space
      (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
        (localization atlas d) i.val).closure hb hb1)
    (physical : letI := charts atlas;
      ∀ z, EuclideanSmoothHolderCore.physical
        (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
          (localization atlas d) i.val).closure hb hb1 output z =
        ChartPairTransfer.pair (atlas.normalizedTubeChart i.val.val)
          (atlas.normalizedTubeChart j.val.val) (fun m => (d.beta i.val m : ℂ)) Fw gw f.val z) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    RegularChartPairTransfer.localPair (carrier).atlas (carrier).localization Fw gw
      (carrier).localView (carrier).localView_injective pairMember i j f = output := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  apply (carrier).localView_injective i
  refine (RegularChartPairTransfer.lift_view _ _ _ _ f).trans ?_
  funext z
  exact ((localView_apply atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap i output z).trans
    (physical z)).symm

theorem combine (X X' Y Y' Z Z' s q : ℝ) (hX : X = X') (bound : X' ≤ s * Y' + q * Z')
    (hY : Y' = Y) (hZ : Z' = Z) : X ≤ s * Y + q * Z := by
  subst hX hY hZ
  exact bound

omit [FiniteDimensional ℝ E] in
/-- Chart-pair rows in the form produced by the polarized chart-pair bound
give the carrier's local pair estimate for the same map and weight. -/
theorem pairBound_of_rows (Fw : M → M) (gw : M → ℝ)
    (pairMember : letI := charts atlas;
      letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
      ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support (carrier).atlas (carrier).localization j)),
      ChartPairTransfer.pair ((carrier).atlas i) ((carrier).atlas j)
        ((carrier).localization.cutoff i) Fw gw f.val ∈ ((carrier).localView i).range)
    (strong : ℝ) (remainder : tubes → tubes → ℝ)
    (rows : letI := charts atlas; ∀ i j : tubes, ∀ u : SchwartzJetSpace.supportedCore
        (ChartLocalization.localSupport (atlas.normalizedTubeChart j.val) (fun m => (d.beta j m : ℂ))),
      ∃ output : EuclideanSmoothHolderCore.space
          (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
            (localization atlas d) i).closure hb hb1,
        (∀ z, EuclideanSmoothHolderCore.physical
          (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
            (localization atlas d) i).closure hb hb1 output z =
          ChartPairTransfer.pair (atlas.normalizedTubeChart i.val) (atlas.normalizedTubeChart j.val)
            (fun m => (d.beta i m : ℂ)) Fw gw u.val z) ∧
        ‖CompactHolderPhysicalBlocks.realize (volume : Measure (Leaf system))
          (unitSlope system positiveStable) (unitLeaves system positiveStable) radial angle
          (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
            (localization atlas d) i) hb hb1 exponent margin output‖ ≤
        strong * ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
            (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
            (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
              (localization atlas d) j) hb hb1 exponent margin () u‖ +
        remainder i j * ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
            (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
            (ConstructedManifoldLocalization.support_compact (fun k => atlas.normalizedTubeChart k)
              (localization atlas d) j) hb hb1 (fun a => exponent a - lossW)
            (fun a => (sub_le_self _ hW.le).trans (margin a)) () u‖) :
    letI := charts atlas;
    letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv;
    ∀ i j (f : SchwartzJetSpace.supportedCore
        (ConstructedManifoldLocalization.support (carrier).atlas (carrier).localization j)),
      ‖CompletedChartPairTransfer.localRealize (carrier).atlas (carrier).localization
        (carrier).localCore (carrier).localBlocks i
        (RegularChartPairTransfer.localPair (carrier).atlas (carrier).localization Fw gw
          (carrier).localView (carrier).localView_injective pairMember i j f)‖ ≤
      strong * ‖(carrier).localBlocks j f‖ +
        remainder i.val j.val * ‖(carrier).weakLocalBlocksW j f‖ := by
  let := charts atlas
  let := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  intro i j f
  have row := rows i.val j.val f
  obtain ⟨output, physical, bound⟩ := row
  have same := localPair_eq atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap Fw gw pairMember i j f
    output physical
  have realized := localRealize_eq atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap i output
  have blocks := localBlocks_eq atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap j f
  have weak := weakBlocks_norm atlas d μE openV region hb hb1 F hr regularT hT hbq hg support
    positiveStable radial angle exponent margin lossH lossW hH hW η cap j f
  exact combine _ _ _ _ _ _ _ _
    ((congrArg norm (congrArg (CompletedChartPairTransfer.localRealize (carrier).atlas
      (carrier).localization (carrier).localCore (carrier).localBlocks i) same)).trans
      (congrArg norm realized)) bound (congrArg norm blocks).symm weak.symm

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrier
