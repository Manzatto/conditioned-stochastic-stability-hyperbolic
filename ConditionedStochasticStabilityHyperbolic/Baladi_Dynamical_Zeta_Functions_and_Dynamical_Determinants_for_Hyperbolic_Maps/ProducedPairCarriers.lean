module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedAnnealedPair

/-! The exact weak carrier of a constructed pair, with inherited parents.
The pair is derived by the application; this adds no analytic input. -/
@[expose] public noncomputable section
open MeasureTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
variable {S H W Z : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [MeasurableSpace Z]
  {i : S →L[ℂ] H} {j : H →L[ℂ] W}
  {law : ℝ≥0 → Measure Z} {probability : ∀ ε, IsProbabilityMeasure (law ε)}
  {genS : ℝ≥0 → Z → S →L[ℂ] S} {genH : ℝ≥0 → Z → H →L[ℂ] H} {R : ℝ}
  (p : Data i j law probability genS genH R)

abbrev weakSpace (_p : Data i j law probability genS genH R) : Type _ := W
@[instance_reducible] def weakNormed : NormedAddCommGroup (weakSpace p) := inferInstance
@[instance_reducible] def weakSemi : SeminormedAddCommGroup (weakSpace p) :=
  (weakNormed p).toSeminormedAddCommGroup
@[instance_reducible] def weakScalar :
    letI := weakSemi p
    NormedSpace ℂ (weakSpace p) := by
  letI := weakSemi p
  infer_instance
@[instance_reducible] def weakUniform : UniformSpace (weakSpace p) :=
  (weakSemi p).toUniformSpace
omit [CompleteSpace S] [CompleteSpace H] in
theorem weakComplete :
    letI := weakUniform p
    CompleteSpace (weakSpace p) := by
  let _ := weakUniform p
  infer_instance
end ConditionedStochasticStabilityHyperbolic.ProducedAnnealedPair
