module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Complex.Basic

/-! Positive deterministic pressure radius supplies nontriviality even for
periodic subordinate blocks; no leading eigenprojection or mixing is needed. -/
public section
namespace ConditionedStochasticStabilityHyperbolic
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem nontrivial_of_positive_spectralRadius (P : H →L[ℂ] H)
    (positive : 0 < spectralRadius ℂ P) : Nontrivial H := by
  by_contra h
  have : Subsingleton H := not_nontrivial_iff_subsingleton.mp h
  have zero : P = 0 := ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
  simp only [zero, spectrum.spectralRadius_zero, lt_self_iff_false] at positive

end ConditionedStochasticStabilityHyperbolic
