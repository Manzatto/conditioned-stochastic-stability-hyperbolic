module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntrinsicJacobian
import all LeanShared.Analysis.GraphLeafNorm
import all LeanShared.Analysis.EuclideanGraphLeaf
import all LeanShared.Analysis.FakeLeafGraph

/-! The graph area formula for independently constructed intrinsic atlas volume. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped Topology Manifold ContDiff ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem EmbeddedVolumeAtlas.intrinsic_area {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (data : EmbeddedVolumeAtlas U Γ) (μ : Measure U) [IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U)
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    (data.intrinsicMeasure μ).map Subtype.val =
      (FakeLeafGraph.asGraphLeaf U Γ hL slope data.embedded.measurableSet b
        (data.embedded.projection_open hL slope)).measure μ := by
  let e := FakeLeafProjectionChart.chart U Γ hL slope (data.embedded.projection_open hL slope)
  let leaf := FakeLeafGraph.asGraphLeaf U Γ hL slope data.embedded.measurableSet b
    (data.embedded.projection_open hL slope)
  have density : IntrinsicCoordinatePatchMeasures.density (Subtype.val ∘ e.symm) e.target =
      leaf.density := by
    funext u
    change (FakeLeafGraph.parameterDomain U Γ).indicator
      (fun v => ENNReal.ofReal (fderiv ℝ (Subtype.val ∘ e.symm) v).toLinearMap.normDet) u =
      (FakeLeafGraph.parameterDomain U Γ).indicator
        (fun v => ENNReal.ofReal (GraphJacobian.density b
          (fderiv ℝ (FakeLeafGraph.heightExtension U Γ hL slope) v))) u
    by_cases hu : u ∈ FakeLeafGraph.parameterDomain U Γ
    · simp only [indicator_of_mem hu]
      exact congrArg ENNReal.ofReal (data.projection_normDet b hL slope hu)
    · simp only [indicator_of_notMem hu]
  rw [data.intrinsicMeasure_eq_projection μ hL slope]
  change (CoordinatePatchMeasure.patch e μ _).map Subtype.val = leaf.measure μ
  rw [density]
  change (((μ.restrict leaf.domain).withDensity leaf.density).map e.symm).map Subtype.val =
    ((μ.restrict leaf.domain).withDensity leaf.density).map leaf.graph
  have inverse_meas : AEMeasurable e.symm ((μ.restrict leaf.domain).withDensity leaf.density) :=
    CoordinatePatchMeasure.inverse_aemeasurable e μ leaf.density
  rw [AEMeasurable.map_map_of_aemeasurable continuous_subtype_val.measurable.aemeasurable
    inverse_meas]
  apply Measure.map_congr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem leaf.measurable_domain] with u hu
  exact FakeLeafProjectionChart.ambient_inverse_eq_graph U Γ hL slope u hu
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
