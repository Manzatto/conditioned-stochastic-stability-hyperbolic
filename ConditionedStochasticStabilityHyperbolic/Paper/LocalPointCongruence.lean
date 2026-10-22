module
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions

/-! Literal process, scale and core changes transport the complete conclusion,
including its spectral witness; no component is reconstructed or weakened. -/
public noncomputable section
open Set MeasureTheory
namespace ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
theorem Point.transport {C D : AbsorbingMarkovChains.CanonicalChain X}
    {R S : ℝ} {A B : Set X} {ν : ProbabilityMeasure X}
    (process : C = D) (scale : R = S) (core : A = B) (point : Point C R A ν) :
    Point D S B ν := by
  subst D
  subst S
  subst B
  exact point

end ConditionedStochasticStabilityHyperbolic.Paper.LocalConclusions
