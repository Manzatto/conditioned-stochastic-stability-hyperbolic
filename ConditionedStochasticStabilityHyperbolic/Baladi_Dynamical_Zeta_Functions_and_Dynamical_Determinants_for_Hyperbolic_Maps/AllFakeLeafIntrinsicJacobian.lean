module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntrinsicProjectionVolume
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafGraphRegularity
public import LeanShared.Analysis.FakeLeafProjectionPairing
public import LeanShared.Analysis.IntrinsicGraphJacobian
import all LeanShared.Analysis.FakeLeafGraph

/-! The intrinsic atlas density equals the actual Gram density of the
constructed graph, by differentiating the unique inverse projection. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped Topology Manifold ContDiff ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem EmbeddedVolumeAtlas.projection_normDet {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (data : EmbeddedVolumeAtlas U Γ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U)
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    {u : U} (hu : u ∈ FakeLeafGraph.parameterDomain U Γ) :
    let e := FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope)
    (fderiv ℝ (Subtype.val ∘ e.symm) u).toLinearMap.normDet =
      GraphJacobian.density b (fderiv ℝ (FakeLeafGraph.heightExtension U Γ hL slope) u) := by
  let h := FakeLeafGraph.heightExtension U Γ hL slope
  let e := FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope)
  have dh : DifferentiableAt ℝ h u :=
    ((data.embedded.heightExtension_contDiffOn hL slope).differentiableOn one_ne_zero u hu).differentiableAt ((data.embedded.projection_open hL slope).mem_nhds hu)
  have graphDerivative : HasFDerivAt (ConeGraphGeometry.graphPoint U h)
      (IntrinsicGraphJacobian.graphDifferential U (fderiv ℝ h u)) u :=
    U.subtypeL.hasFDerivAt.add (Uᗮ.subtypeL.hasFDerivAt.comp u dh.hasFDerivAt)
  have nearby : (Subtype.val ∘ e.symm) =ᶠ[𝓝 u] ConeGraphGeometry.graphPoint U h := by
    filter_upwards [(data.embedded.projection_open hL slope).mem_nhds hu] with v hv
    exact FakeLeafProjectionChart.ambient_inverse_eq_graph U Γ hL slope v hv
  have derivative := (graphDerivative.congr_of_eventuallyEq nearby).fderiv
  change (fderiv ℝ (Subtype.val ∘ e.symm) u).toLinearMap.normDet = _
  rw [derivative, IntrinsicGraphJacobian.normDet_graph U b]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
