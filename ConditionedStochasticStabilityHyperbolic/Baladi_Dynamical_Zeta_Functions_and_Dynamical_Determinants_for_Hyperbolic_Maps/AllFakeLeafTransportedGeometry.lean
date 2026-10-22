module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafProvedGeometry
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Geometry sources are constructed for every actual chart plane, with the
reference Haar measure transported by its given orthonormal coordinates. -/
public noncomputable section
open MeasureTheory Measure
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
variable {E P I ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ P] in
theorem transportedGeometry (planes : I → Submodule ℝ E) (μ : Measure P) [IsAddHaarMeasure μ]
    (coordinates : ∀ i, P ≃ₗᵢ[ℝ] planes i) (basis : ∀ i, OrthonormalBasis ι ℝ (planes i)) :
    ∀ i, ClassicalGeometry (planes i) (μ.map (coordinates i)) (basis i) := by
  intro i
  let : IsAddHaarMeasure (μ.map (coordinates i)) :=
    (coordinates i).toContinuousLinearEquiv.isAddHaarMeasure_map μ
  exact ClassicalGeometry.proved _ _ _
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
