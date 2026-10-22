module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AdaptedTubeUnitCarrierBounds
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCanonicalSameConeCompact
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCompactWeak
public import LeanShared.Analysis.SchwartzAmbientBlocksComparison
public import LeanShared.Analysis.DyadicCompletionComparison
meta import Lean.LibrarySuggestions.Basic

/-! The shared Unit-indexed fake-leaf family has, leaf for leaf, the same
ambient induced volumes as the canonical half-cone family. Hence its blocks
have the canonical norms, its exact weakenings are compact chart by chart,
and the carrier's strong-to-weak inclusion is compact. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "AdaptedTubeUnitCarrierCompact"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierCompact
open LeanShared LeanShared.HyperbolicAdaptedPatchSystem LeanShared.HyperbolicBasicSet
open LeanShared.OrthogonalProductCoordinates AllFakeLeafModel
open AdaptedTubeCarrierLocalization AdaptedTubeCarrierModel AdaptedTubeUnitCarrier
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V₀ : Set M} {base : BasicData (E := E) T Λ V₀}
  {system : PatchSystem base} (positiveStable : 0 < system.framing.stableDimension)

/-- The canonical half-cone leaf family on the unstable plane. -/
abbrev canonicalFamily :=
  AllFakeLeafDyadicDistribution.family (firstPlane system.euclideanDimension)
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (unitCone system positiveStable ()) (leafBasis system)

/-- Unit-indexed chart indices are the canonical leaf indices. -/
abbrev unitEquiv : Heterogeneous.ChartIndex (unitPlanes system) (unitPlus system) ≃
    Index (firstPlane system.euclideanDimension)
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2)) where
  toFun a := a ()
  invFun x := fun _ => x
  left_inv a := funext fun u => by cases u; rfl
  right_inv _ := rfl

theorem measure_eq (a : Heterogeneous.ChartIndex (unitPlanes system) (unitPlus system)) :
    (unitLeaves system positiveStable a).measure volume =
      (canonicalFamily positiveStable (unitEquiv (system := system) a)).measure volume := by
  change (Heterogeneous.leaves (unitPlanes system) (unitPlus system) (unitCone system positiveStable)
      (volume : Measure (Leaf system)) (unitCoordinates system) (unitBasis system)
      (transportedGeometry (unitPlanes system) (volume : Measure (Leaf system))
        (unitCoordinates system) (unitBasis system)) () a).measure volume = _
  rw [Heterogeneous.leaves_measure]
  refine Eq.trans ?_ (AllFakeLeafModel.leaves_measure (firstPlane system.euclideanDimension)
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (unitCone system positiveStable ()) volume (leafBasis system)
    (ClassicalGeometry.proved (firstPlane system.euclideanDimension) volume (leafBasis system))
    (a ())).symm
  congr 1
  exact ((leafBasis system).repr.symm.measurePreserving).map_eq

variable {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff
    (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
    (ProjectionConeTransversality.cone system.euclideanSecondProjection
      (OneStepConePolarization.minusOpening system.rate)))

/-- Unit-family blocks have the canonical block norms. -/
theorem entry_norm {K : Set system.EuclideanModel} (compactK : IsCompact K)
    (t : Bool → ℝ) (margin : ∀ a, t a ≤ b) (f : SchwartzJetSpace.supportedCore K) (j : ℕ × Bool) :
    ‖AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 t margin () f j‖ =
    ‖AllFakeLeafCanonicalDistribution.core (firstPlane system.euclideanDimension)
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (unitCone system positiveStable ()) (leafBasis system) radial angle compactK t f j‖ :=
  SchwartzAmbientBlocksComparison.coreMap_entry_norm (volume : Measure (Leaf system))
    (volume : Measure (firstPlane system.euclideanDimension)) _ _
    (unitLeaves system positiveStable) (canonicalFamily positiveStable)
    (unitEquiv (system := system)) (measure_eq positiveStable) K _ t
    (AllFakeLeafHolderCoreBounds.bounded (unitPlanes system) (unitPlus system)
      (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
      compactK hb hb1 t margin ())
    (AllFakeLeafCanonicalDistribution.bounded (firstPlane system.euclideanDimension)
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (unitCone system positiveStable ()) (leafBasis system) radial angle compactK t) f j

/-- Every exact weakening of a Unit-family chart core is compact. -/
theorem local_compact {K : Set system.EuclideanModel} (compactK : IsCompact K)
    (t : Bool → ℝ) (margin : ∀ a, t a ≤ b) {loss : ℝ} (positive : 0 < loss) :
    IsCompactOperator (DyadicCompletion.exactInclusion
      (AllFakeLeafHolderCoreBounds.coreBlocks (unitPlanes system) (unitPlus system)
        (unitCone system positiveStable) (unitCoordinates system) (unitBasis system) radial angle
        compactK hb hb1 t margin ()) loss positive (fun _ => 0) (fun _ => le_rfl)) :=
  DyadicCompletionComparison.exactInclusion_isCompact_of_entries loss positive (fun _ => 0)
    (fun _ => le_rfl) _ _ (entry_norm positiveStable hb hb1 radial angle compactK t margin)
    (AllFakeLeafCanonicalSameConeCompact.compact_injective (firstPlane system.euclideanDimension)
      (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (unitCone system positiveStable ()) (leafBasis system) radial angle compactK t positive
      (fun _ => 0) (fun _ => le_rfl)).1

end ConditionedStochasticStabilityHyperbolic.AdaptedTubeUnitCarrierCompact
