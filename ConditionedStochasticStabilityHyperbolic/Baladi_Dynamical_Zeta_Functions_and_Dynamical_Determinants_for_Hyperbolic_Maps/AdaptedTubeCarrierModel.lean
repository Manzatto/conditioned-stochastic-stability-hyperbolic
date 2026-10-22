module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseImageModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafHolderCoreBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedHalfConeData
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeCarrierLocalization
public import ConditionedStochasticStabilityHyperbolic.Paper.LinearRechartedNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedLinearFractionalCalculus
public import LeanShared.Geometry.FractionalScalarLinearRechart
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
public import LeanShared.Analysis.OneStepConePolarization

/-! The physical carrier on the adapted tube atlas. The manifold is linearly
recharted onto the adapted Euclidean model, the noise family and weight are
the literal recharted ones, the localization uses the literal tube cutoffs,
and every chart carries the SAME fake-leaf data: leaves in the unstable
plane, plus cone the half cone around the stable axis, minus cone the
one-step polarization cone. These are exactly the parameters of the
polarized chart-pair bound. -/
@[expose] public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeCarrierModel
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.OrthogonalProductCoordinates AllFakeLeafModel AdaptedTubeCarrierLocalization
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base} (atlas : ChartAtlas system)

/-- The noise family read in the adapted Euclidean model. -/
abbrev maps {r : ℝ} (F : Paper.RegularNoise.Maps (E := E) (ι := ι) T r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T) :
    letI := charts atlas; Paper.RegularNoise.Maps (E := system.EuclideanModel) (ι := ι) T r :=
  F.linearRechart atlas.originalModelEquiv regularT
    (Paper.RegularNoise.proved_linearFractionalCalculus atlas.originalModelEquiv r)

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem smoothT (hT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T) :
    letI := charts atlas;
    ContMDiff (𝓘(ℝ,system.EuclideanModel)) (𝓘(ℝ,system.EuclideanModel)) 1 T := by
  let := charts atlas
  exact ((LinearRechartedManifold.identity_forward (M := M) atlas.originalModelEquiv).of_le
    (by simp)).comp (hT.comp
      ((LinearRechartedManifold.identity_backward (M := M) atlas.originalModelEquiv).of_le
        (by simp)))

/-- Leaf parameters: the unstable coordinates. -/
abbrev Leaf (system : PatchSystem base) := EuclideanSpace ℝ (Fin system.framing.unstableDimension)

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem firstPlane_finrank (system : PatchSystem base) :
    Module.finrank ℝ (firstPlane system.euclideanDimension) = system.framing.unstableDimension := by
  rw [firstPlane_dimension, finrank_euclideanSpace_fin]

/-- An orthonormal basis of the unstable plane indexed by unstable coordinates. -/
def leafBasis (system : PatchSystem base) :
    OrthonormalBasis (Fin system.framing.unstableDimension) ℝ
      (firstPlane system.euclideanDimension) :=
  (stdOrthonormalBasis ℝ (firstPlane system.euclideanDimension)).reindex
    (finCongr (firstPlane_finrank system))

variable {radius : ℝ} {tubes : Finset atlas.NormalizedTubeIndex}
  (d : FiniteSmoothCapturePartition.Data (E := E) Λ
    (fun i : tubes => atlas.normalizedTube radius i.val))

/-- Constant chart families. -/
abbrev planes : tubes → Submodule ℝ system.EuclideanModel :=
  fun _ => firstPlane system.euclideanDimension
abbrev plus : tubes → Set system.EuclideanModel :=
  fun _ => ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)
abbrev minus : tubes → Set system.EuclideanModel :=
  fun _ => ProjectionConeTransversality.cone system.euclideanSecondProjection
    (OneStepConePolarization.minusOpening system.rate)

omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem cone (positiveStable : 0 < system.framing.stableDimension) :
    ∀ i, ConeData (planes atlas (tubes := tubes) i) (plus atlas (tubes := tubes) i) :=
  fun _ => AdaptedHalfConeData.halfConeData system.euclideanDimension
    (by rw [finrank_euclideanSpace_fin]; exact positiveStable)

abbrev basis : ∀ i, OrthonormalBasis (Fin system.framing.unstableDimension) ℝ
    (planes atlas (tubes := tubes) i) := fun _ => leafBasis system
abbrev coordinates : ∀ i, Leaf system ≃ₗᵢ[ℝ] planes atlas (tubes := tubes) i :=
  fun _ => (leafBasis system).repr.symm

/-- The fake-leaf family of every tube chart. -/
abbrev leaves (positiveStable : 0 < system.framing.stableDimension) :=
  AllFakeLeafHolderCoreBounds.leaves (planes atlas (tubes := tubes)) (plus atlas)
    (cone atlas positiveStable) (coordinates atlas) (basis atlas)

variable (μE : Measure system.EuclideanModel) [μE.IsAddHaarMeasure]
  {V : Set M} (openV : IsOpen V) (region : V ⊆ d.capture)
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  {r : ℝ} (F : Paper.RegularNoise.Maps (E := E) (ι := ι) T r) (hr : 1 ≤ r)
  (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
  (hT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g : M → ℝ} {q : ℝ} (hbq : b < q)
  (hg : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g)
  (support : tsupport g ⊆ V)

/-- The regular action bounds of the recharted carrier; its window caps the noise level. -/
abbrev bounds :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  ConstructedHolderNoiseAction.bounds μE (fun j => atlas.normalizedTubeChart j)
    (localization atlas d) (tubeChart_mem atlas) openV region hb hb1
    (maps atlas F regularT) hr (smoothT atlas hT) hbq
    (hg.scalarLinearRechart atlas.originalModelEquiv) support

variable (positiveStable : 0 < system.framing.stableDimension)
  (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate)))
  (exponent : tubes → Bool → ℝ) (margin : ∀ i a, exponent i a ≤ b)
  (lossH lossW : tubes → ℝ) (hH : ∀ i, 0 < lossH i) (hW : ∀ i, 0 < lossW i)
  (extraH extraW : tubes → Bool → ℝ) (hEH : ∀ i a, 0 ≤ extraH i a) (hEW : ∀ i a, 0 ≤ extraW i a)
  (η : NNReal) (cap : η ≤ (bounds atlas d μE openV region hb hb1 F hr regularT hT hbq hg support).window)

/-- The physical carrier model on the adapted tube atlas. -/
def model :=
  letI := charts atlas
  letI := LinearRechartedManifold.manifold (M := M) atlas.originalModelEquiv
  ConstructedHolderNoiseImageModel.model μE (fun j => atlas.normalizedTubeChart j)
    (localization atlas d) (tubeChart_mem atlas) openV region hb hb1
    (maps atlas F regularT) hr (smoothT atlas hT) hbq
    (hg.scalarLinearRechart atlas.originalModelEquiv) support η cap
    (volume : Measure (Leaf system))
    (GraphJacobian.densityBound_nonneg (ι := Fin system.framing.unstableDimension)
      (Heterogeneous.commonSlope (planes atlas (tubes := tubes)) (plus atlas)
        (cone atlas positiveStable)))
    (leaves atlas positiveStable) (plus atlas) (minus atlas) (fun _ => radial) (fun _ => angle)
    exponent margin lossH lossW hH hW extraH extraW hEH hEW

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeCarrierModel
