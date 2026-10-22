module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafConstructedArea
public import LeanShared.Geometry.AffineGraphGeometry
public import LeanShared.Analysis.AffineGraphMeasure
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! Literal induced volume on a full affine graph is its actual positive
constant-Jacobian parameter measure. No affine area formula is assumed. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem inducedVolume_affineGraph (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ)
    (b : OrthonormalBasis ι ℝ U) (μ : Measure U) [μ.IsAddHaarMeasure] :
    inducedVolume U μ (AffineGraphParameter.carrier U L v) =
      (μ.withDensity (fun _ => ENNReal.ofReal (GraphJacobian.density b L))).map
        (AffineGraphParameter.point U L v) := by
  have embedded : C1Embedded U (AffineGraphParameter.carrier U L v) :=
    AffineGraphParameter.embedded U L v
  have slope := AffineGraphParameter.slope U L v
  have area := embedded.constructed_area μ b (norm_nonneg L) slope
  exact area.symm.trans (AffineGraphParameter.measure U L v (norm_nonneg L) slope
    embedded.measurableSet b (embedded.projection_open (norm_nonneg L) slope) μ)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
