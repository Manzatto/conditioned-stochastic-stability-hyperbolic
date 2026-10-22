module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafAffineVolume

/-! Actual induced-volume integrals on parallel affine graphs reduce to
parameter integrals with a proved strictly positive constant Jacobian. -/
public noncomputable section
open MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem integral_affineGraph (U : Submodule ℝ E) (L : U →L[ℝ] Uᗮ) (v : Uᗮ)
    (b : OrthonormalBasis ι ℝ U) (μ : Measure U) [μ.IsAddHaarMeasure]
    (f : E → ℝ) (continuous : Continuous f) :
    (∫ x, f x ∂inducedVolume U μ (AffineGraphParameter.carrier U L v)) =
      GraphJacobian.density b L*(∫ u, f (AffineGraphParameter.point U L v u) ∂μ) := by
  have pointContinuous : Continuous (AffineGraphParameter.point U L v) :=
    (IntrinsicGraphJacobian.graphDifferential U L).continuous.add continuous_const
  rw [inducedVolume_affineGraph U L v b μ,
    integral_map pointContinuous.measurable.aemeasurable continuous.aestronglyMeasurable,
    withDensity_const,integral_smul_measure,
    ENNReal.toReal_ofReal (GraphJacobian.density_nonneg b L),smul_eq_mul]
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
