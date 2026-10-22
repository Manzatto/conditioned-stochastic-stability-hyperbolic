module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafConstructedArea
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAreaSources
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! All geometric source fields are proved for the actual Haar-normalized
intrinsic induced volume, independently constructed from embedded charts. -/
public noncomputable section
open Set MeasureTheory Measure
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem ClassicalGeometry.proved (U : Submodule ℝ E) (μ : Measure U) [IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ U) :
    ClassicalGeometry U μ b :=
  ClassicalGeometry.of_area U μ b (fun _ embedded _ hL slope =>
    embedded.constructed_area μ b hL slope)
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
