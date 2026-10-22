module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Probability.UniformNoiseCube

/-! Literal regular-noise laws from normalized Lebesgue cube volume.
Positive scales have full support and finite constant density; the zero
scale is the Dirac law at the zero control. -/
public noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {ι : Type*} [Fintype ι]

@[expose] def uniformCubeLaws : Laws (ι := ι) where
  law := NoiseCubeRescaling.uniformCubeLaw
  probability := NoiseCubeRescaling.uniformCubeLaw_probability
  full_support := NoiseCubeRescaling.uniformCubeLaw_openPos
  bounded_density ε positive := by
    obtain ⟨c, finite, identity⟩ := NoiseCubeRescaling.uniformCubeLaw_density (ι := ι) ε positive
    exact ⟨fun _ => c, measurable_const, c, finite, fun _ => le_rfl, identity⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
