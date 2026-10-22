module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafConstructedArea
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafGraphRegularity
public import LeanShared.MeasureTheory.ParametrizedImmersionTransport
import all LeanShared.Analysis.FakeLeafGraph
import all LeanShared.Analysis.GraphLeafNorm
import all LeanShared.Analysis.EuclideanGraphLeaf

/-! Actual physical graph parametrizations carry precisely the independently
constructed leaf volume, with their actual rectangular differential density. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem C1Embedded.graph_parametric_volume {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) (μ : Measure U) [μ.IsAddHaarMeasure]
    {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    EmbeddedSubmanifoldVolume.volume U μ Γ =
      ((μ.restrict (FakeLeafGraph.parameterDomain U Γ)).withDensity
        (IntrinsicCoordinatePatchMeasures.density
          (ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope))
          (FakeLeafGraph.parameterDomain U Γ))).map
        (ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope)) := by
  let b := stdOrthonormalBasis ℝ U
  rw [← embedded.constructed_area μ b hL slope]
  change Measure.map _ ((μ.restrict _).withDensity _) = Measure.map _ ((μ.restrict _).withDensity _)
  congr 2
  funext u
  change (FakeLeafGraph.parameterDomain U Γ).indicator
    (fun x => ENNReal.ofReal (GraphJacobian.density b
      (fderiv ℝ (FakeLeafGraph.heightExtension U Γ hL slope) x))) u = _
  by_cases hu : u ∈ FakeLeafGraph.parameterDomain U Γ
  · rw [indicator_of_mem hu]
    rw [IntrinsicCoordinatePatchMeasures.density, indicator_of_mem hu]
    have regular := ((embedded.heightExtension_contDiffOn hL slope).differentiableOn
      one_ne_zero u hu).differentiableAt ((embedded.projection_open hL slope).mem_nhds hu)
    have derivative := U.subtypeL.hasFDerivAt.add
      (Uᗮ.subtypeL.hasFDerivAt.comp u regular.hasFDerivAt)
    have equal : fderiv ℝ
        (ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hL slope)) u =
        IntrinsicGraphJacobian.graphDifferential U
          (fderiv ℝ (FakeLeafGraph.heightExtension U Γ hL slope) u) := derivative.fderiv
    rw [equal, IntrinsicGraphJacobian.normDet_graph U b]
  · simp only [IntrinsicCoordinatePatchMeasures.density, indicator_of_notMem hu]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
